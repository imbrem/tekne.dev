---
title: Fun with Sentence Embedding
edited: '2024-06-04'
published: '2023-10-08'
---

It’s been a while! I got back from [ICFP'23](https://icfp23.sigplan.org/) where I presented my work on [Explicit Refinement Types](https://dl.acm.org/doi/10.1145/3607837), got buried in PhD work, and now need to get back to writing. So to celebrate my return, let’s do something a little different, and write some Python.

Embedding vectors are, in my opinion, one of the most fascinating concepts in all of computer science. The idea is relatively simple: we have some distribution of inputs, often coming from a discrete space, such as:

- Words, sentences, or paragraphs of text, perhaps in various different languages
- Small computer programs
- Images, or fragments of video
- Nodes in a graph, for example in a social network
- DNA fragments

We want to take a piece of data from our distribution and map it to a vector in a (usually) high-dimensional latent space, called the embedding vector. Of course, while in theory this mapping could be anything, in practice, we often want to ensure that “similar” inputs map to “similar” vectors, where similarity of vectors is often defined as “pointing in roughly the same direction” (i.e. [cosine similarity](https://en.wikipedia.org/wiki/Cosine_similarity)).[^1] Such mappings can be used for various applications, including:

- Evaluating translation pairs, since translated text should be “similar” to the original
- Performing sentiment and topic analysis on text
- With models having correlated embedding vectors, tasks like synthesizing or describing images using text
- Clustering datasets for further analysis

A good embedding vector, in short, summarizes the meaning of the input data in a way which is amenable to analysis using the usual linear algebra toolkit.

In this article, we’re going to compute the embedding vectors of some sentences and play around with the results, hopefully learning a thing or two along the way. We’re going to be using Google Colab; a complete notebook can be found [here](https://colab.research.google.com/drive/1akqIHZr5AwzfqQf4xlaW9QXK3f9DyYVp?usp=sharing), though I recommend following along yourself. Datasets and figures can be found in the [following repository](https://github.com/imbrem/fun-with-embedding/).

# Generating and Visualizing Embeddings

We’ll start by connecting to a runtime with an accelerator (a TPU or T4 GPU are both fine). We’ll then install all the packages we’ll use by running the following cell:

```python
# Hugging Face's state-of-the-art framework for embeddings
!pip install sentence_transformers
# For exploring high-dimensional data
!pip install sklearn
# For plotting
!pip install matplotlib
!pip install seaborn
```

We can use the `sentence_transformers` package to easily download and test out various models. Looking around for something to compute the embedding vectors of simple sentences, we might stumble across [all-MiniLM-L6-v2](https://huggingface.co/sentence-transformers/all-MiniLM-L6-v2), which maps sentences and paragraphs to a 384 dimensional dense vector space. Good enough for this experiment; let’s load it up as follows:

```python
from sentence_transformers import SentenceTransformer
model = SentenceTransformer('sentence-transformers/all-MiniLM-L6-v2')
```

Using this model is as easy as

```python
encoded = model.encode([
    "Using this model is as easy as passing in an array of strings!",
    "Each string is converted to an embedding vector, and the whole result is returned as a numpy array.",
])
```

Note that in this case the embedded outputs are unit vectors, which can be thought of as points on the 384-dimensional sphere; we can verify this by running

```python
import numpy as np
import math

for vec in encoded:
  assert math.isclose(np.linalg.norm(encoded[0]), 1.0)
```

Alright, let’s try some more interesting experiments! I’m going to fire up ChatGPT and generate lists of about 100 random sentences about various topics and stick it into [a JSON](https://github.com/imbrem/fun-with-embedding/blob/main/facts.json) with the following structure:

```json
{
    "mathematics": [
        "The Pythagorean theorem states that in a right triangle, the square of the hypotenuse is equal to the sum of the squares of the other two sides.",
        ...
    ],
    "china": [ ... ],
    ...
}
```

We can get this data as a Python object by simply running

```python
import requests

response = requests.get("https://raw.githubusercontent.com/imbrem/fun-with-embedding/main/facts.json")
facts = response.json()
```

Let’s start out by building a dictionary of embeddings as follows:

```python
embeddings = {
    topic: model.encode(sentences) for topic, sentences in facts.items()
}
```

So, we’ve now got a bunch of high-dimensional vectors, which is nice. But how can we make sense of them?

Let’s start by using [t-SNE](https://en.wikipedia.org/wiki/T-distributed_stochastic_neighbor_embedding) to visualize our vectors by mapping them to points in 2D space. We’ll begin by collecting our embeddings and their topics into a list, as follows:

```python
embedding_list = np.array([embedding
             for embeddings in embeddings.values()
             for embedding in embeddings])
topics = [topic
          for (topic, sentences) in facts.items()
          for _ in sentences]
```

Note that we put our embeddings into an array so it works with the t-SNE API.

Now, all we have to do is feed this into [scikit-learn](https://scikit-learn.org/stable/)’s t-SNE implementation as follows:

```python
from sklearn.manifold import TSNE
tsne = TSNE(n_components=2, random_state=23)
vis_dims = tsne.fit_transform(embedding_list)
```

Here, `n_components` is the number of dimensions we want to map each embedding vector to, in this case two for a 2D plot. We also fix a `random_state` for reproducibility. Plotting this is as easy as

```python
import seaborn as sns
import matplotlib.pyplot as plt

# Set a large figure size to visualize things better
plt.figure(figsize=(10, 7))
sns.scatterplot(x=vis_dims[:, 0], y=vis_dims[:, 1], hue=topics)
# Put the legend to the upper left, rather than on the graph
# where it covers points
plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left')
plt.show()
```

Running this, we obtain the following plot:

<div style="text-align: center">
<img src={embedding_tsne} alt="t-SNE projections of the embeddings of the sentences in facts.json, color-coded by topic" style="max-width: 70%"/>
</div>

As we can see, the points corresponding to various topics are nicely clustered together, with the broader “topic clusters” of "STEM and geography also visible (cuisine showing up around the boundaries of geography).

# Classifying Embedding Vectors by Topic

So far, this is all qualitative; for a first attempt at making this quantitative, let’s say we manually label some proportion $p$ of our sentences; using this data, how well can be train a model to, given an embedding, predict which topic the unlabelled sentences are about?

To establish some lower bounds on this, let’s try a simple classification method suitable for high-dimensional data like embedding vectors, namely, the venerable [Support Vector Machine](https://en.wikipedia.org/wiki/Support_vector_machine), or SVM. In particular, we’ll define a function as follows:

```python
import numpy as np
from sklearn.model_selection import train_test_split
from sklearn.svm import SVC
from sklearn.metrics import classification_report, accuracy_score

def svc_accuracy(p_train: float, random_state=23, print_acc=True):
  # Randomly partition our data into a training and testing set
  X_train, X_test, y_train, y_test = train_test_split(
      embedding_list,
      topics,
      test_size=1.0 - p_train,
      random_state=random_state)
  # Train an SVM with a linear kernel to do classification
  # `C` here is the *regularization parameter*, which determines
  # the trade-off between minimizing classification error on the
  # training data and achieving a wide margin between the classes
  # to be separated (in embedding space), which tends to lead to
  # better generalization.
  clf = SVC(kernel='linear', C=1)
  clf.fit(X_train, y_train)

  # Predict on the test set
  y_pred = clf.predict(X_test)

  # Compute how well we did
  accuracy = accuracy_score(y_test, y_pred)
  if print_acc:
    print(f"Accuracy: {accuracy}")
    print(classification_report(y_test, y_pred))
  return accuracy
```

Running it with a typical train-test split of 0.8-0.2…

```python
>>> svc_accuracy(0.8)
Accuracy: 0.9791666666666666
                        precision    recall  f1-score   support

                africa       0.92      1.00      0.96        11
       category theory       1.00      1.00      1.00        30
             chemistry       1.00      1.00      1.00        20
                 china       1.00      1.00      1.00        17
      computer science       0.96      1.00      0.98        26
electrical engineering       1.00      0.94      0.97        17
                 ghana       1.00      0.89      0.94        19
        indian cuisine       1.00      1.00      1.00        13
                 japan       1.00      0.95      0.98        22
           mathematics       1.00      1.00      1.00        16
                salmon       1.00      0.94      0.97        17
                 sushi       0.91      1.00      0.95        10
                   usa       0.92      1.00      0.96        22

              accuracy                           0.98       240
             macro avg       0.98      0.98      0.98       240
          weighted avg       0.98      0.98      0.98       240
```

As we can see, it’s doing pretty well! Let’s say we want to save work on all that manual labelling, and only want to do about 100 sentences (giving us, on average, about 10 sentences in each topic). We obtain:

```python
>>> svc_accuracy(0.1)
Accuracy: 0.9424326833797586
                        precision    recall  f1-score   support

                africa       0.78      0.97      0.86        75
       category theory       1.00      1.00      1.00       113
             chemistry       1.00      0.97      0.99        79
                 china       0.88      0.99      0.93        71
      computer science       0.85      0.99      0.92        95
electrical engineering       0.97      0.88      0.93        85
                 ghana       1.00      0.83      0.91        83
        indian cuisine       0.94      1.00      0.97        74
                 japan       1.00      0.99      0.99        73
           mathematics       0.94      0.91      0.93        89
                salmon       0.99      0.97      0.98        75
                 sushi       0.97      0.94      0.95        67
                   usa       1.00      0.83      0.91        98

              accuracy                           0.94      1077
             macro avg       0.95      0.94      0.94      1077
          weighted avg       0.95      0.94      0.94      1077
```

Not too bad! Plotting accuracy for values from 0.01 (just a single example per class) to 0.9, taking 10 samples each time[^2], we obtain:

```python
from tqdm import tqdm
points = np.array([
    [prop, svc_accuracy(prop, random_state=state, print_acc=False)]
    for prop in tqdm(np.arange(0.01, 0.9, 0.01))
    for state in range(10, 20)
])
sns.scatterplot(x=points[:, 0], y=points[:, 1])
plt.xlabel("Proportion of labelled data")
plt.ylabel("Accuracy on unlabelled data")
plt.show()
```

<div style="text-align: center">
<img src={svm_accuracy} alt="A plot of an SVM's accuracy at labelling embeddings given a proportion of the training data" style="max-width: 70%"/>
</div>

As we can see, it turns out we don’t need very much labelled data at all to get good results, and, furthermore, that the quality of results is for the most part consistent.

# Figuring out what the topics are

Let’s look at our t-SNE plot again, but this time without the labelling:

```python
sns.scatterplot(x=vis_dims[:, 0], y=vis_dims[:, 1])
plt.plot()
```

<div style="text-align: center">
<img src={tsne_unlabelled} alt="t-SNE projections of the embeddings of the sentences in facts.json" style="max-width: 70%"/>
</div>

We can make out some clusters that are obvious to the eye, but it’s certainly a lot less clear what is what. One technique we could use, qualitatively, is to pick out random points from each “cluster” and look at what sentence they correspond to. This method can be further enhanced by playing with the hyperparameters of t-SNE, and even by using 3D visualization; in the end, we might be able to come up with the topics we want to later feed our classifier.

Another method is to use unsupervised learning to “discover” topics using only our embedding vectors. There are many methods to attempt this, but, keeping in the spirit of this post, let’s consider one of the simplest to apply, [K-means clustering](https://en.wikipedia.org/wiki/K-means_clustering). To use `scikit-learn`’s `Kmeans` class, we’ll need to provide an `n_clusters` parameter to determine how many clusters it should attempt to find. Let’s start out with 2, since the data in our t-SNE plot seems broadly divided into a left and right hand side: we simply need to run[^3]:

```python
from sklearn.cluster import KMeans
kmeans = KMeans(n_clusters=2,
                n_init=10,
                init='k-means++',
                random_state=23).fit(embedding_list)
```

The field `kmeans.labels_` maps each index in `embedding_list` to its cluster number, in this case 0 or 1. To figure out what clusters K-means has detected, we can print out a _contingency matrix_, which will tell us what proportion of each topic has landed in each cluster, as follows:

```python
import pandas as pd
contingency_table = pd.crosstab(topics, kmeans.labels_)
contingency_prop = contingency_table.div(contingency_table.sum(axis=1),
                                         axis=0)
plt.figure(figsize=(10, 7))
sns.heatmap(contingency_prop, annot=True)
plt.xlabel("Unsupervised label")
plt.ylabel("Topic")
plt.plot()
```

This produces

<div style="text-align: center">
<img src={contingency_matrix_2} alt="A contingency matrix for K-means clustering of our dataset into two clusters" style="max-width: 70%"/>
</div>

It seems that K-means has quite neatly separated out STEM topics from cultural topics, this being the main split in the dataset. Interestingly, some sentences about the US are put into the STEM cluster; we can examine these by pooling our sentences into an array and indexing as follows:

```python
sentences = np.array([sentence
          for sentences in facts.values()
          for sentence in sentences])
sentences[(topics == "usa") & (kmeans.labels_ == 1)]
```

Most of these sentences seem to be about the legal, educational, and transportation systems of the US. It is interesting that no other country’s sentences get put into this cluser. Let’s now see if we can subdivide culture into “region” and “cuisine” clusters: by setting `n_clusters=3`, we obtain

<div style="text-align: center">
<img src={contingency_matrix_3} alt="A contingency matrix for K-means clustering of our dataset into three clusters" style="max-width: 70%"/>
</div>

It seems to work quite well, except that some sentences about Japan are cross-listed as being about cuisine instead. Listing these sentences with

```python
sentences[(topics == "japan") & (kmeans.labels_ == 1)]
```

we indeed see various sentences about Japanese cuisine, but also a few about topics such as etiquette ('Japanese etiquette places a strong emphasis on respect, politeness, and consideration for others') and pop culture ('Japanese pop culture includes J-pop music, fashion trends, and a fascination with cute characters, known as kawaii').

Let’s now try setting `n_clusters=13`, which is the real number of topics:

<div style="text-align: center">
<img src={contingency_matrix_12} alt="A contingency matrix for K-means clustering of our dataset into twelve clusters" style="max-width: 70%"/>
</div>

It seems to recover exactly the input topics, except that Ghana and Africa are considered a single topic, whereas category theory is split into two topics. Running it again with a different seed (`random_state=24`) to see if this result is stable, we obtain:

<div style="text-align: center">
<img src={contingency_matrix_12_24} alt="A contingency matrix for K-means clustering of our dataset into twelve clusters, with a different random seed" style="max-width: 70%"/>
</div>

Here, Ghana and Africa are again only partially distinguished, and the separation between topics is a little less clear (e.g., there is more overlap between matheamtics and computer science). Category theory is now considered only a single topic.

Finally, let’s try setting `n_clusters=20`, and seeing if we recover any useful distinctions not actually present in our manual labelling:

<div style="text-align: center">
<img src={contingency_matrix_20} alt="A contingency matrix for K-means clustering of our dataset into twenty clusters" style="max-width: 70%"/>
</div>

It seems we’ve done so! Africa and Ghana are now recognized as separate topics, and there is little confusion between topics, with topics instead split into sub-topics. For example, topic 3 seems to be about signal processing, control systems, and digital electronics as a subtopic of electrical engineering ('Semiconductor manufacturing involves the fabrication of integrated circuits and microchips using advanced processes and clean rooms.') while topic 7 seems to be mainly about electricity itself ('Electricity is a fundamental form of energy that powers a wide range of devices and systems in modern society.'). Topic 14 is about the application of category theory to computer science, as distinct from computer science itself (split into topics 5 and 8).

# Conclusion

So far, we’ve only scratched the surface of the various applications of embedding vectors by exploring some basic techniques of topic clustering. For the next article in the machine learning series, I plan to go over some more challenging problems, such as sentiment analysis, we also, of course, need to continue the optimization series.

[^1]: For various reasons this is often more useful than the usual notion of distance between vectors, but the choice of distance function is often application-dependent.

[^2]: Note that we wrap the iterator over proportions in `tqdm` to give us a progress bar, since I’m impatient.

[^3]: `n_init = 10` is the current default, here made explicit, as it will be changed to `n_init = ‘auto’` in later versions of Scikit, which we have not found to give particularly good results in this case

<script>
    import embedding_tsne from "$lib/assets/fun-with-sentence-embeddings/embedding_tsne.png"
    import svm_accuracy from "$lib/assets/fun-with-sentence-embeddings/svm_accuracy.png"
    import tsne_unlabelled from "$lib/assets/fun-with-sentence-embeddings/tsne_unlabelled.png"
    import contingency_matrix_2 from "$lib/assets/fun-with-sentence-embeddings/contingency_matrix_2.png"
    import contingency_matrix_3 from "$lib/assets/fun-with-sentence-embeddings/contingency_matrix_3.png"
    import contingency_matrix_12 from "$lib/assets/fun-with-sentence-embeddings/contingency_matrix_12.png"
    import contingency_matrix_12_24 from "$lib/assets/fun-with-sentence-embeddings/contingency_matrix_12_24.png"
    import contingency_matrix_20 from "$lib/assets/fun-with-sentence-embeddings/contingency_matrix_20.png"
</script>
