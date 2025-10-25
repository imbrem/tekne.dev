---
title: Fun with (Multilingual) Sentence Embedding
published: '2025-10-25'
---

A while back, I published a brief introduction to sentence embedding, [_Fun with Sentence
Embedding_](https://tekne.dev/blog/fun-with-sentence-embeddings). This time, I'm back from
[ICFP'25](https://icfp25.sigplan.org/), and history doesn't repeat itself, but it does rhyme.

I've used this blog post as an example of how embedding models can be used to learn relatively
complex concepts using very little training data, while, where applicable, being much cheaper (and,
sometimes, simpler!) to use than an LLM with a prompt. 

For example, here's a graph from the previous articles showing how well an SVM on embeddings does at
classifying sentences into various topics. The total number of sentences is 1000, and we get pretty
decent performance even at 5% labelled data, or 50 examples.

<div style="text-align: center">
<img src={svm_accuracy} alt="A plot of an SVM's accuracy at labelling embeddings given a proportion of the training data" style="max-width: 70%"/>
</div>

Given that we have so few examples, one of the core questions in machine learning (which we should
_always_ be asking, even, perhaps especially, when we have a lot of examples!) shows up naturally:
_what_ are we actually learning.

I had an interesting idea for some of experiements to do to figure this out, inspired partly by
that time I used the aforementioned blog post to teach high schoolers about embeddings. It worked
pretty well, but they asked a lot of questions, and more importantly, tried classifying a lot of
weird sentences.

I have no idea what the results here will be; I'm trying to, in the spirit of _Adventures in Type
Theory_, just get ideas out of my head and onto the page. So, without further ado...

# Language and Meaning

- are we learning "sentences about X" or "sentences about X in language Y"?

## Detecting Semantics

- train on one language, test on another
- train on `n` languages, test on `n + k`
    - language clusters:
        - European:
            - English
            - Romance: French, Spanish
            - German
            - How much data do different languages have? E.g. Portuguese, Italian?
        - _Indo_-European:
            - Hindi
            - Urdu
            - Tamil?
        - Semitic:
            - Arabic
            - Hebrew
        - Chinese
            - Cantonese vs. Mandarin?
        - Japanese

## Detecting Language

- how varied do the topics need to be to detect which language we're talking about? not at all?
- what about mixed-language sentences? can we reliably detect those:
    - with on/off SVMs about detecting a given language? this lets us discuss how multi-class SVMs
      actually work.
    - with a mixed bin?
    - what about language families/regions?

# Null

- random sentences will get a category
- come up with a better header. "irrelevant sentences"? "uncategorized"? "no match"? "None"?
    - What does SQL do, again?

## Relevance

- can we effectively learn "sentences in our categories" vs. "sentences not in our categories"?
- do other languages get sent to the null bin, before multilingual training? or are they implicitly
  translated? does this differ based on model type (e.g. multilingual retrieval vs other)
    - Go get a list of model types for this
- SVMs should be nice for this, discuss

## Stereotypes

- other than the completely irrelevant, what about "stereotypical" data
- in short, which stereotypes are bad (this both a safety and performance problem)? Which are good?
- think of a nice example of a good and a bad stereotype here, not too spicy
- what about language stereotypes?
    - are random sentences in language X most often classified into bin Y?
    - e.g., are Chinese sentences about China?
    - What about e.g. Chinese sentences about America?

# Questions for the Audience

Can be a separate blog post...

Should be a separate blog post. But we can stick the pointer here for now, and translate notes over.

## Concept RAG

- Can we query a vector database using an SVM?
    - Is there another ML model which supports efficient queries to the DB of the form:
        - Step 1: train a concept
        - Step 2: query vectors satisfying that concept
    - Other nice-to-haves: intersections with lots of concepts, other things, scoring
    - Different database kinds?
        - Hierarchical Navigable Small World?
        - Inverted File Index?
    - See: 
        - Concept Activation Vectors (CAVs) from interpretability lore
        - Custom query embeddings 
        - Weaviate Hybrid Search
        - Qdrant payload filters
        - Semantic SQL
        - [Compositional concepts](https://www.seas.upenn.edu/~steinad/papers/Compositional_Concepts.pdf)?
- Generative vs. cached lore here? Like a collection of points in a latent space... what's a
  collection of points of interest or known points on a map called? Not really an atlas, and that's
  way too loaded... OpenLatentSpaceMap?

<script>
    import svm_accuracy from "$lib/assets/fun-with-sentence-embeddings/svm_accuracy.png"
</script>
