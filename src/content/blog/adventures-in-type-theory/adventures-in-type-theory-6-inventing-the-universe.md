---
title: Adventures in Type Theory 6 -- Inventing the Universe
published: '2026-08-02'
description: 
categories: []
series: Adventures in Type Theory
uuid: 69ead7ec-f66c-44ad-9387-146a7ebffd96
---

_Time_: 2026-08-02T14:31Z

_Location_: Westminster, London, United Kingdom

_“If you wish to make an apple pie from scratch, you must first invent the universe.”_ -- Carl Sagan

Typing universes are confusing -- or at least they always confused me.
It's something glossed over in introductions to theorem provers
-- which can be, 
and were at least for me, particularly poor introductions to type theory
-- as simply a way to avoid typing out the identity function for each $A : \mc{U}$.
And fair enough 
-- that's why we need them, and they're not that important for most of what you need to do.

But that makes universe levels an _annoyance_, 
rather than an interesting problem in their own right
-- and makes it very hard to think about how you could improve universe levels
while still keeping your type theory sound.
A lot of the ad-hoc attempts break the soundness bit
-- sometimes for theoretical reasons, 
and sometimes because of [integer overflow](https://github.com/agda/agda/issues/5706).

When I started my PhD, I distinctly remember my very first conference: [POPL'22](https://popl22.sigplan.org/) in Philadelphia.
I was just beginning my second attempt at my lifelong dream 
to build a theorem prover
-- my first attempt ending in my master's thesis, 
_Dependent Types with Borrowing_, 
which I'm sure you can find if you look for.

My problem is I didn't know any better, 
and so kept trying to come up with baroque, 
fantastically complex type systems
-- believing the issues with modern formal verification were a type systems issue,
in the way that I believed the issues with systems programming 
were a type systems issue
(the Rust Evangelism Strike Force 
making up a nontrivial proportion of my identity at the time)
and that _surely_ my two favorite things combined would be _even better_ together.

Now I do like the _idea_ of Idris 
-- it's like ice cream and chocolate, which is great
-- I've never actually used it much though, 
so I have no idea if it's like that or more like _bona fide_ chocolate ice cream,
the type which is just brown ice cream, 
which I guess is decent but I'm not particularly a fan of 
because I'd rather just have chunks of chocolate in my ice cream.

The [Idris](https://docs.idris-lang.org/en/latest/tutorial/introduction.html) guys are awesome 
-- so probably the former
-- and then again if its the latter that's fine too I just don't have taste.
I should probably give Idris a serious try and report back.

But what I was doing was a lot more like ice cream on steak,
which is both not very tasty, and against _kashrut_.

So attempt number two was something a little simpler
-- I left the systems programming out, _for now_,
and started trying to write my very first paper,
_Typechecking up to Congruence_,
research I still need to finish
-- on which I gave my very first talk 
at [WITS'22](https://popl22.sigplan.org/home/wits-2022):
an idea which, much later, formed the foundation of attempt three,
which hopefully after a PhD's worth of adventures I'm now not ready for
(no one is ever ready for interesting things)
but rather capable of breaking in new and interesting ways.

Which we'll start writing about soon. 
It's why I'm back, in fact
-- but anything other than a rambling start 
and you'd have to worry whether I was an impostor rather than a mere crackpot,
right?

But yes.

So there was a life lesson embedded not in this talk but surrounding it it
-- Stephanie Weirich was leading an excellent small-group discussion session on 
[The Expression Problem and Theorem Proving (discussion)](https://popl22.sigplan.org/details/wits-2022-papers/2/The-Expression-Problem-and-Theorem-Proving-discussion-)
-- and the issue was that it was not in fact a small group discussion,
since there were a lot of people.

So she asked if anyone wanted to volunteer to see if they could form a splinter group.

Not a _single_ person wanted to talk about typechecking up to congruence
-- but I'm nonetheless proud I asked anyways.

I digress.

Point is all this time spent thinking about MLTT and I still didn't really
_understand_ MLTT 
-- I was poking around with [logrel-mltt](https://github.com/mr-ohman/logrel-mltt),
which eventually formed the model for my Lean 4 formalization of 
[Explicit Refinement Types](https://www.cl.cam.ac.uk/~nk480/ert.pdf).
But like -- what _was_ MLTT
-- Neel kept telling me (and he was right!) 
that I had to first clarify what I meant by MLTT 
before I could clarify what I meant by definitional equality.

My mind kept circling around two things:

- What _is_ a typing universe?

- What I called the _valley problem_
  -- that is, _why_ do we need reduction to be confluent?

The latter led me to the conclusion that
$
\text{``Larry Paulson"} \in \{p \mid \ms{isTrueMeme}(\text{``\{}p\text{\} was right again"}\}
$
-- another particularly important element of this set being Richard Stallman.

The former led me to many meditations on the nature of typing universes,
leading to my very first mention in the academic literature in
Favonia et al.'s excellent paper [An Order-Theoretic Analysis of Universe Polymorphism](https://favonia.org/files/mugen.pdf)
-- my contribution being to stay up late arguing with Favonia about fractal universe levels while not knowing much about what it takes to make a sound universe system.

Anyways
-- many years later, I want to talk about the foundations of typing universes.

And to do that, I need to talk about Cantor's theorem, and the beth cardinals.