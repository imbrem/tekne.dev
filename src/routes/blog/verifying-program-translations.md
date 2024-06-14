---
title: Verifying Program Translations
published: '2024-04-14'
---
Unfortunately, the lingua franca for FFI still remains C. And because that's often not the right
choice... or because we can't help ourselves and need to rewrite it in Rust... we are faced with the
task of rewriting a library. Assuming we resist the temptation to heavily re-architect things, a lot
of this turns into rather repetitive manual copying of functions, definitions, and, if we're being
optimistic, comments. We might want to change stylistic conventions, such as going from `camelCase`
to `snake_case`, as well.

Given a translation, however, how can we determine whether it's _correct_? For example, say we're
told to translate
```python
def fact(n):
    acc = 1
    while n > 1:
        acc *= n
        n -= 1
    return acc
```
ChatGPT 4o (without me directly prompting it...) says an equivalent implementation of this function
in JavaScript is
```js
function fact(n) {
    let acc = 1;
    while (n > 1) {
        acc *= n;
        n -= 1;
    }
    return acc;
}
```
This looks right to me! Let's try evaluating this just to be sure, in Python
```python
>>> [fact(1), fact(2), fact(3)]
[1, 2, 6]
```
and in Javascript, using my browser (Firefox 126.0.1)
```js
>> [fact(1), fact(2), fact(3)]
[ 1, 2, 6 ]
```
By Engineering Induction™[^1], this translation seems about right. Unfortunately, however, these
programs are untyped. Hence, we might be interested in how they behave on ill-formed inputs: for
example, as we'd expect, we have
```python
>>> fact("4")
---------------------------------------------------------------------------

TypeError                                 Traceback (most recent call last)
...
```
errors out. But, JavaScript, which is famed for it's type safety, wouldn't want to just _crash_ like
that...
```js
>> fact("4")
24
```
We are now left to wonder whether this translation is indeed correct or not. The answer is: it
depends! We need a notion of a program's _meaning_ to see if it is preserved by the translation
process. If this sounds familiar, that's because that's how we (should) reason about optimizations,
too.

[^1]: As we learned at UofT, "if it works for 1, 2, and 3, it's good enough for me!"

The simplest possible answer is to require two programs $P$ and $Q$ to agree all the time, including
on the errors. Taken naively, this might be quite difficult if the two languages have different
exception systems, so we might not care about the exception itself, only whether one is thrown.

A more interesting answer is to use _types_. The fact that you can do this even in an untyped
language is now [_cool_ and _popular_](https://www.typescriptlang.org/), but beyond merely
typechecking a program, we might also consider whether two programs $P$ and $Q$ agree for all
_well-typed_ inputs. 

For example, we might annotate our Python as follows:
```python
def fact(n : int) -> int:
    acc = 1
    while n > 1:
        acc *= n
        n -= 1
    return acc
```
ChatGPT says this is
```ts
function fact(n: number): number {
    let acc: number = 1;
    while (n > 1) {
        acc *= n;
        n -= 1;
    }
    return acc;
}
```
in Typescript. Unfortunately, the types have not _quite_ been translated directly: the bottom, for
example, admits `fact(0.5)`, whereas this would be ill-typed for the top[^2]. So we've now
introduced the problem of checking whether our type translations are correct, too!

[^2]: In this case, `int` is a strict _refinement_ of `number`, i.e., types strictly less things.

Another idea is to require $Q$ to _refine_ $P$; that is, to require that, for all correct inputs to
$P$, $Q$ returns the correct result. What counts as a "correct" input can be determined in various
ways:
1. We can say an input is correct if $P$ does not crash
2. We can determine what the correct input is using types
3. We can explicitly write out a set of valid inputs to test

The latter is the simplest, so it's what we'll go with for now: in addition, we can additionally
test that no valid inputs lead to a crash. For brevity, we may also be able to _infer_ valid input
sets based on type annotations to $P$ where no set is otherwise explicitly given.

We now have a skeleton of a test procedure:

- *Given:*
    - Programs $P$, $Q$ which might be in different languages
    - A set of valid inputs $V$ to program $P$
    - A relation $\sim_I$ from inputs to $P$ to inputs to $Q$, where $x \sim_I y$ if $x$ is "the
      same" as $y$, interpreted in a language-specific manner
    - A relation $\sim_O$ from outputs and side-effects of $P$ to outputs and side-effects of $Q$,
      where $E \sim_I E'$ if $E$ is observationally "the same" as $E'$, interpreted in a
      language-specific manner
- *To determine whether $P$ and $Q$ are equivalent*:
    - Verify that for all $x, y$ if $x \in V$, then $x \sim_I y \iff P(x) \sim_O Q(y)$

Implementing this in practice quickly runs into the challenge that $V$ becomes very large very fast:
while a single 32-bit integer input has 4 billion possible inputs to enumerage (already a challenge
on a fast computer for a fast function!), just four such inputs and we're already up to 340
undecillion possibilities. This is usually where I start to talk about model checking and formal
verification. [Since we don't live in that future yet](https://www.youtube.com/watch?v=Tz0clKux3WM),
we can just use [_differential fuzzing_](https://en.wikipedia.org/wiki/Differential_testing) and 
randomly generate inputs $x \sim_I y$ and, for each such input, check $P(x) \sim_O Q(y)$, with the
goal of eventually being able to conclude that the overwhelming majority of such pairs are handled
correctly. Of course, this is assuming that $P$ and $Q$ are deterministic, so that their outputs
can be checked straightforwardly.

...