---
title: Adventures in Type Theory 5; Stream 1 - Bird's Eye View
published: '2025-10-07'
---

_Time_: 2025-10-07T14:04Z

_Location_: above hills above mountains, riding discount Pegasus #PC1820. No fleece in sight.

For what is (hopefully) the last time as a PhD student, I make pilgrimage to ICFP'25. I was supposed
to spend the flight like a good PhD student, writing thesis. _Elas_, I forgot to `pull`. Rookie
mistake.

So now I'm unmoored from the world, with nothing but a pen for my thoughts and no paper to write on.
Such thoughts are fleeting, precious, valuable; brief flashes of exponential flourishing in the
liminal parts of phase space, scrawled on tissue paper and skin, marks long outliving their ink.
Folklore ever cited, never proven. Revolutionary algorithms. Great expectations!

Good thing I've brought my laptop, too. So I can write this instead!

That ever-present human question. _What should I think about?_ Could `$SUBCONSCIOUS_GUY` have
wandered the abstract plane?

Let's get some thoughts down, which can be our first commit, and cook them down, which can come once
we have Internet. I always say I should do this: just _write_, and then cook things down. It's hard
to find an example of the process, too; it's done retrospectively by, say, digging through Tolkien's
notes, but what about the time-honored tradition of a Git history? I should use branches more, too,
and squash my commits. See, this is the raw stuff of thought, the warp and weft and shaggy
typo-ridden fibre of what I only hope can be made into a well-typed tapestry. A typistry, if you
will. I'm saving that one.

# A Pterodactyl's Eye View of Covalence

I've been reading about Jon Stirling's work on Pterodactyl, as I've been thinking about my
`covalence` theorem prover project. I really like his syntax for combining the fields of different
algebraic structures, and relating structures to each other by renaming.

I've been using Lean's `@[to_additive]` a lot recently as part of trying to get the math my thesis
depends on into mathlib (TODO: cite issue), and while it's a great tactic (I like how `guessName` is
syntactic, for convenience, but the actual lemma dictionary is not, which would have been
_terrible_, especially given the namespace changes... it would be really nice to open a section in
the additive namespace of the local namespace; though, and to set a translation for a given
namespace. Maybe there's a way!) I think such things should really be `defeq`s.

Now, `covalence` is extensional, but the `defeq`s matter here too, since we are _not_ univalent, and
while an explicit isomorphism is also nice (and should be an option), in general, an `AddMonoid` is
a monoid with attitude, _not_ a structure isomorphic to a `Monoid`, in my book.

So... how I think of this kind of syntax is, "how do I represent _concepts with attitude_"? How do I
separate the actual mathematical object, the actual semantic blurb, from that concept's _attitude_,
allowing me to shift and translate between attitudes as something less than isomorphism but more
than mere equality?

I've had a lot of shower thoughts about this, for many years, and Pterodactyl and `covalence` have
brought it to a head.

So I want to start writing a demo for `covalence` ASAP. The first thing we need/want is Alethe
input, once the necessary kernel functions are in. Need to go do that.

But we also want specialized languages for specialized tasks.

There's two directions here that I want to explore.

The first is, as in most modern theorem provers, we need a _vernacular_. Since our programming
language is extensional, I really want to think about what kind of vernacular can make best use of
that, how we can best both expose and tame the computational flexibility of extensional type theory.

Now, one of the main appeals of our system design is (hopefully) the ability to emulate regular
intensional code. But for an _intensional_ vernacular, rather than try to reinvent the wheel (and
Jon makes an excellent point about the difficulty of trying to make a good theorem prover and
programming language at the same time, which is doubly true for me considering my lack of
resources!), we want to steal one instead. If we could even parse a small fragment of `.olean`
files... I need to do more homework on this.

# Forests of Ferns

What evolved first, trees or ferns? I think it was the ferns, but I need to look it up.

(TODO: stick result here)

It is strange to be unmoored from the great web of reality "reality" Reality? that we weave. I'm
letting myself be really creative with the feed-text here. Like cooking with fish sauce, right? We
pay for the umami at the end with the fish at the beginning.

The Romans thought fish sauce degraded the human character. Foreign _garum_-eaters-of-rotten-things;
in flagrant violation of both common sense and Aristotelian-Roman-decency, which held the cook in
disdain even on the best of days, let alone in such cases. For it is one thing to beautify the
living, and another to embalm a corpse!

Are not burial rights, burial rites, rights? the first sign of culture, of humanity? Do we not weep
for the Neanderthal, buried among the flowers? Is not the elephant's graveyard a sign?

And so we transcend rotten fish, too. What is is what is. Now to go further and _desire_ such fish;
to have elevated something from its natural state by what, when done in ignorance, is putrefaction?
What a _human_ act.

As can most clearly be seen, I need to organize my thoughts. And I _really_ like Jon Sterling's
`forester` tool to organize one's notes.

I was reading, back in Calabria actually, about _zettelkasten_, and was thinking of making an
SQLite-based `zettel` tool because plaintext is actually not structured enough to be portable, with
a nice entry table and tables of entities and indexes corresponding to semantics and
SQLite-is-what-Excel-should-have-been-because-types-are-good and many other wanderings of my mind,
trapped in the cyclic mirror-halls of perfectionism like a Mentat with the wrong thoughts who is not
a mentat and has a body.

Anyways `forester` does this and is actually usable and used, without the perfectionism. Interesting
use of XSLT, too.

Weighing in on the XSLT deprecation debate while I'm here; I do think the sustainable solution is a
polyfill, but to have a standard library of polyfills shipped with the browser. It's a tiny addition
to the browser bundle, a huge increase in potential functionality (ship an experimental polyfill;
when it gets standardized and battle-tested, now you don't need to fetch it anymore), you can maybe
even use _hashing_ and _formal verification_ (a man can dream, no?), and when it's in the standard
then you don't need to ship it with your site, but you _can_ via a hash-based CDN. 

Though that opens the door to fingerprinting old browsers. 

Lack of available functionality was always a fingerprint vector, though, right?

Anyways I really want to start a Zettelkasten. And I do still want to make my own tool, for SQLite
reasons. I _like_ SQLite, as much as I dislike some bits of SQL.

But some thoughts on Forester.

- Potentially-semantic-but-also-potentially-alphanumeric identifiers like the Stacks project.
  Interesting.

  I like UUID's, though. You can fingerprint them if you don't want to lug around the whole thing,
  and even statically verify intra-database fingerprint uniqueness, and do inter-database
  fingerprint exports. I thought about this a bit. It's a nice quality-of-life-feature.

  But the normal form should be the full UUID.

  I also like content-addressing. But the current format lets you change your cards.

  With content-addressing you need to update the referees, too, and you obviously can't update
  external references.

  An interesting compromise is IPFS style mutable/immutable pairs. You could decentralize it with
  keypairs.

  I quite like the idea of "local decentralization;" the fact that you assume local mostly-trusted
  parts lets you remove a lot of the inefficiencies of the Hobbesian world of blockchains, and now
  the decentralization becomes a tool for interoperability and standardization rather than
  feature-balling.

  It's very POSIXy. And UNIX would be a much nicer place if it started out with strong encryption,
  namespaces, and content-addressing.

- Interesting idea to have different entity types for what are essentially your zettelkasten cards.
  Like the "Person" entity for the head of department at Cambridge.

  Even more interesting idea to link between such databases, in a cool-privacy-preserving-way. I
  like entity IDs. I have a lot of shower thoughts about this I need to just get down, dumb as they
  are, so that we can walk down the long road to _not dumb_. 

  But I also like databases? A table-per-entity-kind? For flexibility, a JSON field? Do we store
  _everything_ in the JSON field, pulling out rows as appropriate? What is index performance like on
  JSON subfields in SQLite?

  How typed do we want our entity? A strongly-typed entity as a _subentity_ of your blob? _Many_
  strongly-typed entities, because mutual inheritance is nice, and never causes any problems for
  anyone? Diamonds are definitely semantic here, so this is _not_ a composition problem.

  And see, we find ourself back to pterodactyl. How to manage diamonds, using _renaming_.

  I think it applies here, quite strongly, in fact.

  Now I'm thinking of a Typescript type being like a schema on my JSON column.

  To Typescript or to native object, that is the question.

  Now consider a table of e.g. unique locations, UUID, latitude and longitude. If I want to
  associate other things with that UUID, that's a foreign key.

  So it's like an association map.

  But of course other tables can also be UUID indexed, and map something else to it.

  So I say I like restaurant X. In the location table, the UUID for restaurant X is its lat-long
  pair. Because in this sense restaurant X _is_ a location. That sounds wrong, that sounds like a
  "has-a" relation, sounds like composition rather than inheritance.

  But a restaurant is a _place_. Switch words, and inheritance seems natural. Places of course have
  a location, but the location is the lat-long pair, the _placeness_ is what puts it in the _place
  table_ the things within have a lat-long pair which may be null because I may not know where that
  place is.

  And places are what the place-functions take, the functions drawing lines and pins on our maps,
  and one day, maybe, letting us conveniently see the lines and pins at the same time without
  opening tabs and waiting for things to refresh because _God forbid_ I see data that's 1 minute out
  of date, let me _wait_ a minute for fresh data from the server instead.

  But what else is a restaurant. It has a name, too, but so should places, NULLably perhaps. And it
  has a category, a subcategory of restaurant, but restaurant is a category of place.

  So should there be a category column in the place table, and no restaurant table? Is the
  restaurant table a view of the place table, with category restaurant?

  Well that's the question, is there unique data related to it that only a restaurant would have,
  some other restaurant table keyed by the restaurant UUID and they have the same UUID so they're
  the same thing, obviously.

  Well some places have reviews, and restaurants are one of those places, so the reviews table can
  have a foreign key there. But that's not an essential nor a specific component of
  _restaurant-ness_; well maybe essential since any restaurant can be reviewed. Even a king's table
  can be criticized by those outside the king's grasp, and how often is food fit for a king's table
  rejected out of principle? I can learn to eat rice, too! To cook for many kings, and eat rice on
  the roads between kingdoms, however, is synthesis, for a rock would be enlightened if it were not
  a rock, but awakened, well... I suppose a stochastic parrot is without ego, but I'm a
  life-affirming man, and without `self` is a sea of meaningless truth whipped up by a storm of
  inchoate inspirations.

  As I was saying. So what goes in the _restaurant_ table? What data is inherent to
  _restaurant_-ness?

  There are some things only (generalized) restaurants have, like menus. But not all restaurants
  have these things, maybe, at least not all of them. So there's tables which, if you are in them,
  you're almost certainly a restaurant, and maybe you should enforce you certainly are a restaurant,
  but that's not restaurant-ness.

  Maybe a category of restaurant-ness, and then these foreign tables for each type of
  restaurantly-metadata, the whole soup making up an implicit, extendable, JSONic object with UUID
  keys for concepts and a schema with unknown fields ignored? This seems like the way.

  So "restaurant" is a _subtype_ of "place", and there are projections of this subtype that the main
  type does not have.

  But... categories. One place can have many categories, not just `NULL` and `RESTAURANT`, which are
  of course macros for their randomly-generated concept UUIDs, because why would we use an existing
  database like OpenData, and subject ourselves to the vagaries of SPARQL.

  Imagine, and hear me out, a great repository of such UUIDs, strictly but extensibly typed as
  described below, validated by distributed or centralized processes, with signatures so that the
  final choice of trust is, as is right and proper, dumped upon the user, such that sane defaults
  may protect them, and centralized CAs nonetheless act as sad shadows of the
  web-of-trust-which-could-have-been. Though I need to finish updating my laptop (I run Arch btw),
  because my time was taken up updating my keys with `sudo pacman-keys --refresh-keys` while waiting
  for the Uber during my last moments connected to Computer Lab Wi-Fi before my return, and that
  takes _forever_. Like how can downloading and checking these little kilobyte-size primes and
  elliptic-curve points take longer than hundreds of megabytes of movie. _It's distributed and
  poorly funded_, they say (I need to learn how `refresh-keys` actually works and where it's
  hosted...), perhaps? Well... have you ever _torrented_ a movie? _Elas_ for GPG!
  
  I wonder if those lost keys I made in first year, back when I still larped as an emacs user, have
  finally expired. Right. Restaurants.
  
  There's sushi restaurants and tapas and vegan restaurants, and of course Vietnamese restaurants
  where I can get some good _garum_. Categories within restaurant, but some of these categories are
  cultural, and different cultures will recognize different categories, and databases will be
  prepared by different cultures, and just _imagine_ what that committee looks like??? Han Cuisine
  Normalization. I suppose some of my relatives already don't really distinguish between Chinese and
  Japanese food...

  Obviously the categories of place are culture dependent too. Point is we have lots of categories.
  So I don't want a category column since I don't want a unique category mapping.

  So what about a _set_ of restaurants, containing place UUIDs. And place UUIDs are just object
  UUIDs, which are all UUIDs, so we've got our hierarchy here.

  The tables draw from that great, global, universal set, and the relation is established, the olog
  is drawn, and our ontologies may duel in the psychic plane. Your restaurant set versus mine, union
  or intersection, _et cetera_ and _ceterus paribus_.

  Whoever is reading the Git history of what is dawning on me could be a very nice article on the
  concept of _zettlekasten_ and ologs, a paragraph or two explaining each, the links between them
  inferred, once I am re-connected to the Internet and can access a copy of Spivak, I am so sorry.

  Eventually I'm going to write down me E-graph zettlekasten idea in full, but for my sake and for
  your sake we need to build up there, get out of the hall of mirrors, and make an SQLite database
  with a cards column and a virtual hierarchy to replace a file full of text files, and maybe an
  index on dates to show _why_ we would do such a thing and not just use the venerable file full of
  text files, IO performance and copy-pastability aside, since versioning SQLite is a pain and dbhub
  is gone from this world, too far ahead of it's time.

  There was something related to DuckDB related to dbhub, but I have forgotten.

  Imagine I could use my zettlekasten, right about now. I might even know if I'm spelling that word
  correctly.

  That is how I know that I must begin. Perhaps this article will even be about that!

  We'll see how much I end up procrastinating on presentation, thesis, and `covalence`, in that
  order of importance, though I really want Alethe input in showable form by ICFP if a miracle
  occurs...

  Maybe this article will be about _that_! Then things will be good. That's the _thinking man's_
  topic choice.

- So `forester` is a very tree-like naming scheme, but of course it's a DAG. This is using the fact
  that an _unfolded_ DAG is always a tree; just duplicate your nodes. But that's a very
  content-addressed way of thinking, and these notes aren't content-addressed.

  Same for inter-tree citations. No content-address, what if it changes? Disappears? And now there's
  just one place to get it from, that you can trust, at least! Trust to show you what the author
  wants you to see, of course, rather than what they _wanted_ you to see, before they edited those
  nodes.

  I think about this problem often for academic citations. DOIs are great and all, sure, but
  centralization aside... like... _why not hashes_.

  Why not give the traditional citation, _and then a version hash_. You can update your hash, if you
  want to. It's just like Unison!

  Why does Unison, a programming language for servers of all things, do this, and it's a great idea
  but servers change and fix bugs all the time, but not literally _everyone else_???

  I really like content-addressing, and I need to write about it more, and get my ideas straight.

  "Rambling" is a word for roaming around; through these rambles, hopefully I can roam to an idea I
  can actually explain with a straight face. The address of my content, if you will. I'd show myself
  out, but this is the abstract plane, the digital world. There is no way out (but through).

- Browser polyfills, like XSLT. What could WASM do for browser polyfills?

    - I'm just going to start with the mad dream of JS itself being a browser polyfill over
        sufficiently advanced WASM-GC. What would you need for a standard JS compilation scheme?

        I'm thinking rather than extending WASM, optimized intrinsics of some kind. But of course we
        need data-structures, things which would become the archetypes of our objects and somesuch.

        How could you, in a generic, JITtable-way, tell WASM-GC that you need _archetypes_. It's an
        interesting design space.

        But this is nonsense at this point. Just a vague direction, a tangent vector along a latent
        manifold, a little curved line orthogonal to the vast current, a fish seeking out the
        riverbank, dragged forward from ever-joining-streams to ever-widening-rivers, to the sea,
        which is not bounded but bounds, and yet is barred, and only the living may cross, if they but
        leave some of their nature behind.

        Or maybe a more appropriate analogy for ECMAscript is the River Styx?

        No. They are burdened by the past, but they flow towards life.

    - Now an interesting idea is _content types_. You could accelerate them by swapping them for
        compiled modules, which are provable compilations of the appropriate WASM. But the issue is:

        - Either the WASM becomes nondeterministic. We've already started on this path with
        platform-dependent SIMD instrinsics and strictness flags, so we can walk it

        - Or those compiled modules need to, even if e.g. hardware accelerated, produce _bit-by-bit_
        identical results. 
        
        And yet... even the most basic anti-aliasing functions in the terrible world of GPUs, where
        _some people_ not only ship around a smorgasbord of bytecode and platform-dependent API
        calls, but, in imitation of cardinal sin, ship around _source text in poorly specified
        high-level languages with versioning problems_, and name themselves after a twice-forgotten
        pretender-deity of all-consuming decay who eats his children until they, despite him,
        enslave man in ignorance and powerlessness and call it a Golden Age because those men were
        in a sense _happy_? And give us boxes, and I'm sure shiny sapphire-screened tablets, and
        scrolls, and we scroll them, when we would dare _learn_ to harness fire, to make order from
        the random flashes of blinding fate which burn our forest and melt sand into smoky prophecy,
        fulguritic prefigurations of clarity?

        Those? _Those_ are ill-specified. They draw polygons in some places. Circles in others.

        How would you even _start_ specifying that, except with the very highest-level API calls?

        Now a codec is not like that. But the Path of the Codec is dark, and veers even beyond the
        GPU, down to secret metal, and twisting dark forests too, filled with wide vines and
        treacherous cables between authenticated trees.

        It could not have been, and it cannot be. But maybe one day...

        Perhaps when consumer CPUs can trivially decode video, on that fateful day, when we need
        accelerated formats for clunky petabyte-sized 3D tensors of hyper-sensory data, on _that_
        day, there will be a hashed specification, and a polyfill-fallback.

        Who am I kidding? That tensor will probably be encrypted, and everyone except you will hold
        the key.

        Prometheus was the only one of you worth anything, but that was an older generation, in an
        older time. Will any of the new bloods on Mount Olympus step up to the plate?

    - Since I'm obviously feeling very Greco-Roman today for some reason (stopping in Antalya?),
        what about 3D formats. Statues and stuff. I don't know.

        I'm thinking about those diffusion models for low-poly 3D models. Metamodel. Heh.

        Anyways you can make cool statues out of those. Generate "marble statue of X" as an image,
        mesh-n-texture, and you can make a hall out of those. I wanted to make a _Piranesi_
        simulator, but that found its way to the Great Backburner.

    -  Where does my stream-of-consciousness flow now. We already discussed streaming formats, and
       the woes and perils of the accelerator. Non-streaming formats are better. Imagine polyfilled
       JPEG-XL. Or, like, that weird super-simple PNG-like with better compression, forgot the name.

       I mean... ZSTD with dictionaries is like this. Ah. I see what I was trying to recall. Next
       point!
- So the other idea I wanted to get out was about _Kolmogorov complexity_.

  Kolmogorov complexity is an uncomputable quantity: the Kolmogorov complexity of some string $s$ is
  the size of the smallest program $P$ which generates $s$. Of course, this depends on the execution
  environment and language itself. People play all kinds of games with Turing machines, in the
  theoretical world. More interestingly is the Compression Olympics, trying to get 1GB of Wikipedia
  into as small of an x86 executable as possible.

  It was thinking of this that got me down the path to E-graph representations of denotational
  Montague semantics for natural language. I will eventually write that down without jargon, and
  with a nice and intuitive data structure, God-willing. But I have to endure writing it down
  _poorly_ first. Look. Word pointers. Idea. A shower of rain is lost without a bucket.

  Tears in rain? Bucket.

  Our social media posts are tears in a bucket. 
  
  Speaking of which, anyone here remember ForgeBukkit?

  Now... what about the Kolmogorov complexity of WASM?

  Write your answer into a buffer. No need for a special API, either, just set aside a growable
  memory space as your buffer, call `halt(final_size)` when you're done, now that WASM3 is a thing.

  - Worried about resource exhaustion? Execution is deterministic; tag your file with `gas` and
    `memory_use` and something like the Solana gas annotator thing (or a timeout as a linear
    function of `gas` if you want to be fast rather than strict).

    `memory_use` includes outputs, so no ZIP-bombs either! Or you can separate those, too. Count
    that memory space as separate. But then `halt(final_size)`...

    So just (remember, deterministic) tag with a `final_size` too, and now it's just `halt`.

    Truncate the output buffer past there.
  
  But the interesting thing to think about here is the interaction with (one of) my Very Favorite
  Ideas of All Time (we can shorten this to "one of my ideas of all time"), _content addressing_.

  So... ye olde `memcpy_content(HASH, destination)`. Address space general, of course. That's one
  start! `register_hash(HASH, content)` is another...

  Hey wait! A WASM file doesn't need to compress one thing... it can compress _many_.

  A table of hashes it provides. Functions to provide those hashes. 

  You know the output is valid because it hashes right.

  And it depends on other hashes, provided by others, disk or cache or network or IPFS or subprogram
  or whatever.

  This is the way.

  And of course... hashes of other programs, and meta-execution. WASM modules and components; fetch
  the hash of a component, instantiate it, and speak to it.

  So if you want a ZIP file, fetch the hash of a ZIP implementation. ZLIB, etc etc.

  Now there's an issue here: I'd really like to hardware accelerate ZIP and ZLIB (though this
  increases attack surface, so make it optional!) versus run the WASM.

  But how do we deal with gas here?

  Instrument foreign function calls and pass in the gas usage? First run can be zero to fill in the
  instrumentation, in non-strict mode.

  Subtract that much gas in WASM mode; error out if the execution uses more than that gas.

  But for _native_ mode, check whether the gas is in some budget model for a given algorithm, and if
  so, dispatch to accelerator, and again just subtract gas.

  So output of deterministic but failure mode for out-of-gas is now semideterministic...

  Which means fingerprinting using compression failures...

  Force over-provisioning gas by a safe-factor and enforce over-provisioning by hyper-strict mode
  with an RNG? But users don't want random compression failures...

  Push out the nondeterminism by using time-to-gas?

  But now accelerator quality is not only fingerprinted, but means time-to-gas estimates will be way
  off (overestimates, as we want)...

  I suppose the solution is just to start by fetching a component and executing the gasified version
  like any other, but adding a way to give a component a gas budget. Strict mode always uses the
  entire gas budget.

  Then acceleration can play with strict mode, somehow, and maybe require an overprovision.

  I guarantee taking Xkb to Ykb requires at most Z operations.

  Or something.

  Yaar. Point is we can instrument functions with their expected inputs and outputs, since again,
  determinism.

  But I like this "network compression" idea. With WASM linking, we can recover the concept of a
  single archive. Like a ZIP archive, too. The root can just decompress to a JSON describing the
  internal filesystem, with pointers of "things to unhash". It's deduplicated and everything.

  We can have a section for external dependencies, which are also deterministic... it's great!

# Yelling at Clouds

Alright... we're landing, going through the clouds now, into Turkey. So time to bring this narrative
back to Earth, and eventually, we should figure out what this article should actually be about.

Pre-article plane conversations! They were fun! And weird...

The guy sitting next to me is going to Afghanistan, with his girlfriend (!), to study weaving under
the masters. Now, I've been to Lebanon many times, but still, that seems a lot more risky for him,
but for _her_, and _them_? He's of Afghan heritage, but his answer to whether this is safe is "I
guess I'll find out." Though presumably, he claims, foreign currency is needed, and he just wants to
learn weaving.

Afghan weaving. What a tale. Anyways I bored him describing compiler intermediate representations,
evading quite a few attempts to change the topic before I relented. He got me started talking about
compilers. This is _his fault_, and I apologize for nothing.

Afterwards, spoke to the ladies in front of me, getting some dental work done in Turkey, and one,
later, some wrinkle treatment, sisters, very very nice people! Also Nietzsche fans, it seems. This
is a really weird row. Anti-aging is (quite literally) life-affirming. Alas that it is my current
(to a degree theological; also, after a hundred thousand years, what is left) position that, in this
world, this is impossible, but, in the words of Bryan-Johnson, "don't die." 

Now the cosmetic version of that... it doesn't necessarily increase lifespan, it may even decrease
it. And yet, it increases the time you are _you_, or at least look like _you_, where _you_ are who
you want to be, because to quote Pindar, _become who you are_. Though, yet, every day, we are _made
who we are_, and we need to fight and yet also yield, like iron and not like glass. Or something.

Still in the clouds!

So those were my plane-mates. There was also a nice old man and his wife whom I swapped seats with,
going to Turkey for vacation. Alas, I will not be stopping in Turkey, though I miss it dearly. I do
want to ride there, eventually. Perhaps on a repaired Z650, or a greater bike of greater times to
come. Or perhaps on my Gladius, which I have come to love, for while it was riding my KTM Baby Duke
that I grew up, it was the Gladius which carried me, in a streak of blue smoke (I _really_ should
have got the ABS version... need to always remember not to skid, and be gentle with the brakes...),
into a new age.

It is 2025-10-07T16:17Z. And that's about two hours of stream-of-consciousness on a plane. I'm at
22% battery, since Node makes even text-entry and refreshing eat some CPU power, methinks, and now
suddenly feeling a bit seasick. Which I never really feel on a plane.

This was an interesting plane ride. Just came up with the section title, which will hopefully _not_
be preserved. There has so far been one and only bad influence in my life which has caused me to
write titles like that. But thus we pick up marking habits, that we be known by them. Humanities
titles, man...

Excited to see some old friends. Back in Humanities class (what a class name... imagine "STEM
class..." I guess that was science class, except we never learn technology or engineering and saw
only memorized fruits of science and elementary mathematics... imagine STEAM class. STEAMpunk. Heh.
I will stop. What about humanities which are _not_ arts. Is that what STEAM excludes? History? Is
STEAM STEM + humanities, but forward facing only?) 

Greenfield Community School, was it in Jebel Ali, need to look it up. It started in a hotel, you
know, I think anyways. Courtyard Mariott? Is that still open? I tried to sell "respects your
freedom," GNU site design services to non-technical people who would otherwise use Wix. Didn't work.
Got half a site done for free. Didn't help that I was learning HTML as I went along. Later in life,
it was not often I met people who shared my childhood heroes; to discuss this while weaving through
Seattle traffic and updating priors left right and center, that is what it means to be alive.

It has been almost a decade, 8 years, since I've met many people from that time. Will see a few now,
some others I kept in touch with. Lot of calls to make.

Antalya is shrouded with rain-clouds, which we fly through. Just a few drops streak by the window.
Now it forms a river, a single line, and rivulets are dragged back from it. It breaks into two, and
re-forms. It's raining upwards.

The ground is greenhouses and roads. Would that my ancestors could have seen this. The cloud-puffs
fly by, reminding me how fast we're going. A snail's pace, compared to how fast we _were_ going.

The roads get closer. There's turbulence, and the cars remind me just how fast that still is. We're
landing.

I remember one of the first time I landed in Dubai, to visit before we move there. People are
clapping now. Not really then, though. Was scary how close we passed buildings. I found it strange;
never experienced that before on a flight. Think it was a rough landing.

The asphalt is wet. This device is about to shutdown. That asphalt was dry. Someone else learned
ephemerality from wet asphalt.