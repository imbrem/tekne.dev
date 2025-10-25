---
title: Embedding the Null Hypothesis
published: '2025-10-25'
---

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