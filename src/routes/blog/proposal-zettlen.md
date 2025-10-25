---
title: Proposal: Zetteln
published: '2025-10-25'
---

- Inspired wikis
- But _private_, not _public_
- Idea for tool:
    - Dolt backend
    - _Later_: local WASM SQLite; not _quite_ local first since Dolt is the source of truth
        - Do Androids Dream of ElectricSQL?
- Related work:
    - [Zettelkasten](https://zettelkasten.de/) site
        - One difference is we want to _integrate_ AI
    - Jon Sterling's [Forester](https://www.forester-notes.org/index/index.xml) tool
        - Similarities:
            - Private vs. public linking
        - Differences (theoretical):
            - Private _first_, versus originally based on Stacks (but see intellectual heritage from
              [evergreen notes](https://www.forester-notes.org/andymatuschak/index.xml) to
              Zettelkasten)
            - SQL over XML
        - Differences (practical):
            - Con: _Has_ a backend, so a bit less decentralized/harder to host
            - Neutral: version control baked in, but "so does text"
            - Pro: query-first design, allows things like querying events at a given date
            - Neutral: UUIDs as names
                - _Not_ content-addressed as we want more evolution; that's a _backend_ thing via
                  Dolt's prolly tree
                - No short identifiers, use a fingerprint if you really want that
                - Allows merging forests safely always
                - _Encourages_ multiple naming schemes over UUIDs since UUIDs are cumbersome
                    - No need to rename things, just update links
                - Names have no semantic meaning; but this is the same as Stacks project IDs
                - See the note on the [Intellectual
                  Junkyard](https://www.forester-notes.org/QHXS/index.xml), encourages federation.
                  Eventually, we might like to federate with Forester instances!

                  We should think about the problems Stirling brings up.
                - No identity between the same thing in different Zettelkasten, instead we have
                  links, like a union-find. I was going to say E-graph, but it's like union-find
                  because
                    - No congruence yet, but see The Big Idea
                    - The points-to relationship matters semantically, maybe, or at least
                      historically, though for _queries_ we only care about the generated
                      equivalence relation (many points-to-relations) can generate the same
                      equivalence relation
            - Neutral: rather than use things like XSLT, we have a full Javascript system
                - Con: adds complexity
                - Pro: applets and graphs are nice, the structure is in the database not the XML

- Bigger ideas:
    - Layered wikis, some public, some private
    - Public on DoltHub; in general, SQL over XML
    - ChatGPT integration, view as _refinement_ pipeline, where "slop" _congeals_ into actual notes
      and idea webs
      - Eventually want some symbolic structure, but that's The Big E-Graph Idea. See, this would be
        the center of my Zettelkasten, which I need to make so I can see the graph:
        - The Big E-Graph Idea, splits into:
            - Analog/intuition/embedding: zettelkasten, wikis, and the evidence network
                - Personal, Intellectual Development, "Personal" as in meme-person: zettelkasten +
                  wikis
                - Science: `scrapebook`, content-addressing
                    - Also, content-addressed citations! Need to get that rant online...
                - AI: concept RAG lore
            - Digital/logical/programming: The Index
                - Prover: `covalence`
                - Compilers: `isotope`, SSA lore (PhD thesis goes here!)
            - Philosophy (meta): 
                - something something Lambek, something something Spivak
                - generalized physics between the platonic and the analog
    - See, this should be a zettelkasten. But it's semi-public on Git, which is _different_ from if
      it was an actual zettelkasten. I'm imagining a similar idea as a branch on the appropriate
      public zettelkasten on DoltHub

- Technical fun things later no time sad; see this is why we need Zettelkasten though!
    - SQLite WASM using pages is fun
        - Can Dolt WASM using pages be more fun?
        - Tfw rewrite Prolly trees in Rust... "only" 500 kloc... ooh
          [look](https://crates.io/crates/prollytree)
          - Can we then just use Git as our backend, and do everything in WASM?
            - [why am I like this?](https://github.com/petersalomonsen/wasm-git)