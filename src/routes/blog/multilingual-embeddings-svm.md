---
title: Do Embeddings Speak the Same Language?
published: '2025-10-25'
---

TODO: re-work as "proposal" and publish, separate from polished experiment section...

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

TODO: do second pass: many experiments on this theme. One (closely related set) per article.

I had an interesting idea for some of experiements to do to figure this out, inspired partly by
that time I used the aforementioned blog post to teach high schoolers about embeddings. It worked
pretty well, but they asked a lot of questions, and more importantly, tried classifying a lot of
weird sentences.

I have no idea what the results here will be; I'm trying to, in the spirit of _Adventures in Type
Theory_, just get ideas out of my head and onto the page. So, without further ado...

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
    - want language similarity axes, and also language data axes (per model)?
        - study language similarity _using_ embeddings?
- Compare models (e.g. retrieval, other kinds)

## Detecting Language

- how varied do the topics need to be to detect which language we're talking about? not at all?
- what about mixed-language sentences? can we reliably detect those:
    - with on/off SVMs about detecting a given language? this lets us discuss how multi-class SVMs
      actually work.
    - with a mixed bin?
    - what about language families/regions?

<script>
    import svm_accuracy from "$lib/assets/fun-with-sentence-embeddings/svm_accuracy.png"
</script>
