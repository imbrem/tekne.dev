---
title: Querying Concepts
published: '2025-10-25'
---

# Concept RAG

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
