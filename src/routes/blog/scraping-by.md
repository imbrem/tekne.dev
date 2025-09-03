---
title: Adventures in Type Theory 3 — Scraping By
published: '2025-09-03'
---
_Location_: [Boulangerie aux délices de Souffel](https://maps.app.goo.gl/2vb9qMHP9eSuZTTr6)
(48.62627, 7.72929)

_Time_: 2025-08-27T12:04+2

The van will be here any minute now.

So much to tell.

Yesterday, while meditating upon scraping, I decided to do some frontend.

Surely, if all my friends are jumping off a bridge, that bridge must be on fire! So I decided to
indulge in a spot of _vibe coding_ with Claude.

So I'm vibing. 

I get a call. The clutch repair is ready, and it's time to bid Woustviller goodbye.

I ride off on my freshly repaired Gladius. So far, so good.

It's really hot. I take off my jacket. I feel the wind. I'm alive, and we're riding to Mulhouse.
Tomorrow, the Alps await.

I pull up to the [gare de péage de Schwindratzeim](https://maps.app.goo.gl/GLNweHJZ4ERnHrYC8). 

It's filled with police and customs officers.

Catching sight of me, they motion me to pull over, wide-eyed.

A cloud of white smoke catches up to me as I pull to a stop. There's oil everywhere. 

My rear wheel is completely soaked.

<div style="text-align: center">
<img src={oil_spill} alt="The Gladius missing its drain plug" style="max-width: 70%" />
</div>

And that’s how I learned that French customs, perhaps uniquely in the world, are empowered to
conduct searches anywhere in the country, not just at the border.

Van's here, yo.

# A Chat at the Pâtisserie

_Location_: [Boulangerie Pâtisserie Berg Woustviller](https://maps.app.goo.gl/3iR1iHs9AqidEsHv6)
            (49.07644, 7.02056)

_Time_: 2025-08-26T15:30+2

I've spent a solid chunk of my youth thinking about _scraping_. If I ever see a paper copy of
[_Milliyet_](https://www.milliyet.com.tr/), I think I'll cry.

Thanks to the influence of a certain [Professor
Berkovitz](https://philosophy.utoronto.ca/directory/joseph-berkovitz/)[^1], I know just enough about
the philosophy of science to be dangerous. I promise these are related. Maybe.

Today we're meditating on an SQL schema for observations on the world, analyses of those
observations, and transformations on the resulting data. In particular, everything in this section
really is a half-baked meditation for a project I'm working on: I hardly know SQL!

_Health warning_: as I said, all the SQL here is vibe-coded, and potentially rife with bugs. This is
an _extremely_ early stage experiment!

The concrete application here is scraping:
- **Observations**: opening a page and seeing what HTML response comes back.
- **Transformations**: deterministic steps like extracting plain text from HTML.
- **Analyses**: nondeterministic or open-world steps like ML inference or human labels.
- And we might further **transform** the analysis, e.g. compute a mean or graph sentiment.

## Basic Schema

So, a basic schema might look like
```sql
CREATE TABLE IF NOT EXISTS ops (
  op_key        BLOB PRIMARY KEY,   -- 32B unique key
  op_class       TEXT NOT NULL,     -- This op is a transformation, analysis, or an observation

  op_type       TEXT NOT NULL,      -- e.g. 'http_fetch','html_to_text','llm_infer','human_label'
  tool_id       TEXT NOT NULL,      -- e.g. 'requests_v1','bs4_v1','rules_v2'
  params_json   TEXT,               -- canonical JSON (sorted keys, stable forms)

  observed_at   TEXT,               -- optional wall clock; MUST be NULL unless observation

  CHECK ( op_class IN ('transformation', 'analysis', 'observation')  )
  CHECK ( (op_class = 'observation') OR (observed_at IS NULL) )
);

CREATE TABLE IF NOT EXISTS op_outputs (
  op_key  BLOB NOT NULL,     -- producing op
  idx     INTEGER NOT NULL,  -- output slot: 0,1,2,...
  data    BLOB,              -- arbitrary bytes; may be NULL
  PRIMARY KEY (op_key, idx)
);

CREATE TABLE IF NOT EXISTS op_inputs (
  op_key              BLOB NOT NULL,     -- consumer op
  idx                 INTEGER NOT NULL,  -- consumer input slot (0,1,2,...)
  producer_op_key     BLOB NOT NULL,     -- producing op (may itself be an alias)
  producer_output_idx INTEGER NOT NULL,  -- producing output slot
  PRIMARY KEY (op_key, idx)
);
```
We note the following important design decisions:

- We use the usual relational pattern for multiple inputs and outputs.
- Every observation, analysis, and transformation has a unique key, so we can merge SQLite files
  from different databases.
- The input to every operation is a vector of outputs from other operations, plus parameters.

So, for a scraping experiment, we might have our database containing operations of the form
- `fetch_http` (observation) with URL/user-agent params; outputs headers and bytes.
- `extract_text_from_html` (transformation) consumes HTML and outputs text.
- `split_text_into_sentences` (usually transformation) consumes text; outputs sentences.
- `embed_sentences` (transformation) outputs embeddings.
- A manual labeling pass is an analysis (nondeterministic selection), not an observation.


On the other hand, this framework is perfectly generic. For example, we might apply this framework
to a lab experiment:
- Observe raw sensor data (e.g., the voltage in a thermocouple).
- Transform to the measured quantity via calibration (e.g., the temperature this corresponds to).
- Analyze the transformed data (e.g., fit a regression).

Since transformations are pure, we'd like to deduplicate them: two equal transforms with the same
inputs produce the same outputs. We can do this by adding a field `input_digest` and requiring that
a transformation’s key is its digest:
```sql
CREATE TABLE IF NOT EXISTS ops (
  op_key        BLOB PRIMARY KEY,   -- 32B unique key
  op_class       TEXT NOT NULL,     -- This op is a transformation, analysis, or an observation

  op_type       TEXT NOT NULL,      -- e.g. 'http_fetch','html_to_text','llm_infer','human_label'
  tool_id       TEXT NOT NULL,      -- e.g. 'requests_v1','bs4_v1','rules_v2'
  params_json   TEXT,               -- canonical JSON (sorted keys, stable forms)

  input_digest  BLOB NOT NULL,      -- NEW: SHA-256 hash of (op_type, tool_id, params_json)
                                    -- followed by (input len, input bytes) concatenated in 
                                    -- slot order

  observed_at   TEXT,               -- optional wall clock; MUST be NULL unless observation

  CHECK ( op_class IN ('transformation', 'analysis', 'observation')  )
  CHECK ( (op_class = 'observation') OR (observed_at IS NULL) )
  -- NEW: a transformation is keyed by its input
  CHECK ( (op_class = 'transformation') = (op_key = input_digest) )
);
```
In general, we want to index on our input digest, so that we can, e.g., query for all observations
of a given thing, even if each has a unique ID (being an observation rather than a transformation):
```sql
CREATE INDEX IF NOT EXISTS idx_ops_inputdig     ON ops(input_digest);
```

We also add a content-addressed artifact store for caching large blobs (and the ability to purge
bytes later):
```sql
/* =======================
   ARTIFACTS (content-addressed bytes)
   ======================= */
CREATE TABLE IF NOT EXISTS artifacts (
  artifact_hash  BLOB PRIMARY KEY,   -- 32B sha256(bytes)
  bytes          BLOB                -- payload; may be NULL (purged)
);

CREATE VIEW IF NOT EXISTS artifact_sizes AS
SELECT artifact_hash, length(bytes) AS size_bytes FROM artifacts;
```

(We still store operation outputs as raw bytes. If you want to return cached data, put its hash in
data and write the bytes to artifacts.)

_Fun exercise_: how could we garbage-collect the `artifacts` table?

## Ground Truth

We want to be able to, for any operation, quickly query the set of observations it ultimately
depends on. We can do this by adding a `ground_truth` field to our schema:
```sql
CREATE TABLE IF NOT EXISTS ops (
  op_key        BLOB PRIMARY KEY,   -- 32B unique key
  op_class       TEXT NOT NULL,     -- This op is a transformation, analysis, or an observation

  op_type       TEXT NOT NULL,      -- e.g. 'http_fetch','html_to_text','llm_infer','human_label'
  tool_id       TEXT NOT NULL,      -- e.g. 'requests_v1','bs4_v1','rules_v2'
  params_json   TEXT,               -- canonical JSON (sorted keys, stable forms)

  input_digest  BLOB NOT NULL,      -- SHA-256 hash of (op_type, tool_id, params_json)
                                    -- followed by (input len, input bytes) concatenated in 
                                    -- slot order

  ground_truth  BLOB,               -- NEW: 32B; NULL only if synthetic / no provenance

  observed_at   TEXT,               -- optional wall clock; MUST be NULL unless observation

  CHECK ( op_class IN ('transformation', 'analysis', 'observation')  )
  CHECK ( (op_class = 'observation') OR (observed_at IS NULL) )
  CHECK ( (op_class = 'transformation') = (op_key = input_digest) )
);
```
If our operation does not depend on _any_ observation, we obviously want `ground_truth` to be
`NULL`. On the other hand, for a _single_ observation, it makes sense for `ground_truth` to be the
`op_key` of that observation.

For _multiple_ observations, however, we need some kind of way of keeping track of the _set_ of
observations we're working with. We could:
- Have a separate ground truth table containing records `(operation, observation)`, but the size of
  this table can, in the worst case, grow quadratically with the number of operations
- Have a separate table defining _sets_ of ground truth observations, given by their hashes

Let's go with the latter
```sql
CREATE TABLE IF NOT EXISTS observation_sets (
  set_hash      BLOB NOT NULL,    -- SHA-256 hash of the keys in this set in sorted order
  member        BLOB NOT NULL,    -- `op_key` which is a member of this set 
  PRIMARY KEY (set_hash, member)
);
```

We'll have the convention that: 
- the set `{observation_id}` is just represented as the observation ID
- the set `∅` is represented as `NULL`
- An operation encapsulates its sub-ops: for an observation `id`, `ground_truth = {id}` even if its
  inputs contain a whole pipeline. For a non-observation,
  $$
  \mathrm{ground}(o) = \bigcup_{(i, j) ∈ \mathrm{inputs}(o)}\mathrm{ground}(i)
  $$

It's up to user-code to compute the appropriate hash and, if necessary, update the
`observation_sets` table. So notice we end up with SQL

```sql
CREATE TABLE IF NOT EXISTS ops (
  op_key        BLOB PRIMARY KEY,   -- 32B unique key
  op_class       TEXT NOT NULL,     -- This op is a transformation, analysis, or an observation

  op_type       TEXT NOT NULL,      -- e.g. 'http_fetch','html_to_text','llm_infer','human_label'
  tool_id       TEXT NOT NULL,      -- e.g. 'requests_v1','bs4_v1','rules_v2'
  params_json   TEXT,               -- canonical JSON (sorted keys, stable forms)

  input_digest  BLOB NOT NULL,      -- SHA-256 hash of (op_type, tool_id, params_json)
                                    -- followed by (input len, input bytes) concatenated in 
                                    -- slot order

  ground_truth  BLOB,               -- 32B; NULL only if synthetic / no provenance

  observed_at   TEXT,               -- optional wall clock; MUST be NULL unless observation

  CHECK ( op_class IN ('transformation', 'analysis', 'observation')  )
  CHECK ( (op_class = 'observation') OR (observed_at IS NULL) )
  -- NEW: an observation is equal to its own ground truth
  CHECK ( (op_class = 'observation') = (op_key = ground_truth) )
  CHECK ( (op_class = 'transformation') = (op_key = input_digest) )
);
```

So we can just drop the `op_class` field and replace it with views:
```sql
CREATE TABLE IF NOT EXISTS ops (
  op_key        BLOB PRIMARY KEY,   -- 32B unique key

  op_type       TEXT NOT NULL,      -- e.g. 'http_fetch','html_to_text','llm_infer','human_label'
  tool_id       TEXT NOT NULL,      -- e.g. 'requests_v1','bs4_v1','rules_v2'
  params_json   TEXT,               -- canonical JSON (sorted keys, stable forms)

  input_digest  BLOB NOT NULL,      -- SHA-256 hash of (op_type, tool_id, params_json)
                                    -- followed by (input len, input bytes) concatenated in 
                                    -- slot order

  ground_truth  BLOB,               -- 32B; NULL only if synthetic / no provenance

  observed_at   TEXT,               -- optional wall clock; MUST be NULL unless observation


  -- NEW: an observation is equal to its own ground truth, _and_
  -- only an observation may have a non-null `observed_at`
  CHECK ( (op_key = ground_truth) OR (observed_at IS NULL) )
);

-- Classify each op: transform / observation / analysis
CREATE VIEW IF NOT EXISTS v_ops_class AS
SELECT
  o.*,
  CASE
    WHEN o.op_key = o.input_digest THEN 'transform'
    WHEN o.ground_truth = o.op_key THEN 'observation'
    ELSE 'analysis'
  END AS op_class
FROM ops o;
```

A view to directly look up the ground truth of a given operation might look like:
```sql
/* ============================================================
   v_op_observations
   ------------------------------------------------------------
   Expands each op’s ground_truth into the observations it
   depends on. Usage:
       SELECT observation
       FROM v_op_observations
       WHERE op_key = :op;

   Conventions:
     • Observation o:   ground_truth = o.op_key
     • Non-observation:
         - Synthetic:   ground_truth IS NULL
         - Singleton:   ground_truth = <obs_id>
         - Composite:   ground_truth = <set_hash>, with members in observation_sets
     • Singletons are NOT in observation_sets.

   Logic:
     • LEFT JOIN on observation_sets:
         - Composite → rows per member
         - Singleton → COALESCE picks ground_truth
     • Synthetic ops excluded.
   ============================================================ */
CREATE VIEW IF NOT EXISTS v_op_observations AS
SELECT
  o.op_key                           AS op_key,
  COALESCE(s.member, o.ground_truth) AS observation
FROM ops AS o
LEFT JOIN observation_sets AS s
  ON s.set_hash = o.ground_truth
WHERE o.ground_truth IS NOT NULL;
```

## Aliases

Sometimes you want to _box_ a whole sub-pipeline behind a single, higher-level operation so you can
reason with (and share) a simpler graph. That’s what **aliases** are for.

- An alias operation has its own inputs/params/key but delegates semantics to an existing op’s outputs.
- Aliasing is **orthogonal** to class: an op can be a transform, analysis, or observation **and** be
  an alias. You still classify via `input_digest` and `ground_truth`.
- We **materialize** aliases by copying the target’s outputs into the alias at creation time (no
  alias chasing on reads).
- Later, you can drop the inner subgraph in exports/snapshots and keep only the alias rows + their
  copied outputs if you don’t need the full trace.

To support this, add `alias`:

```sql
CREATE TABLE IF NOT EXISTS ops (
  op_key        BLOB PRIMARY KEY,   -- 32B unique key

  op_type       TEXT NOT NULL,      -- e.g. 'http_fetch','html_to_text','llm_infer','human_label'
  tool_id       TEXT NOT NULL,      -- e.g. 'requests_v1','bs4_v1','rules_v2'
  params_json   TEXT,               -- canonical JSON (sorted keys, stable forms)

  input_digest  BLOB NOT NULL,      -- SHA-256 hash of (op_type, tool_id, params_json)
                                    -- followed by (input len, input bytes) concatenated in
                                    -- slot order

  ground_truth  BLOB,               -- 32B; NULL only if synthetic / no provenance

  observed_at   TEXT,               -- optional wall clock; MUST be NULL unless observation

  alias         BLOB,               -- NEW: which operation this is an alias of, if any

  CHECK ( (op_key = ground_truth) OR (observed_at IS NULL) )
);
```

This matters because what you call an “observation” is often a **calibrated** result rather than raw
sensor bytes (e.g. cleaned HTTP responses, factory-calibrated instruments). Aliasing lets you
publish the calibrated result as *the* observation while the raw steps remain optional but still
machine-readable when present.

In general:

* An alias operation can always be an **observation**.
* An alias operation can be an **analysis** if all of its *internal-only dependencies* (those not
  already implied by the alias' inputs) are analyses.
* An alias operation can be a **transformation** if all of its internal-only dependencies are
  transformations.

We use the inclusions

```
Transformations ⊆ Analyses ⊆ Observations
```

and classify each alias by the minimal class consistent with its dependencies.

### Example: boxing a two-step transform

```
ComplexOp(A, B, C) := SimpleOp( SimpleOp2(A, B), C )
```

Here `A, B, C` can be anything (including observations). Then:

* `ComplexOp` can always be an observation.
* `ComplexOp` can be an analysis if `SimpleOp` and `SimpleOp2` are both analyses.
* `ComplexOp` can be a transformation if `SimpleOp` and `SimpleOp2` are both transformations.

Edge cases:

* If an operation appears both as a direct dependency of `ComplexOp` and inside one of its inputs’
  transitive dependencies, it still counts toward classification (because it is directly required by
  the alias).
* Every operation is considered a transitive dependency of itself.

### Example: calibrated temperature as the observation

```
MeasureTemperature() := ComputeTemperature( MeasureResistance(), GetCalibration() )
```

* `MeasureResistance` = observation (hardware).
* `GetCalibration` + `ComputeTemperature` = transformations.

Here we define `MeasureTemperature` as an **alias** of `ComputeTemperature`. This lets us query
temperature measurements directly, abstracting away the raw resistance reading. It also makes
heterogeneous measurements comparable: e.g. `MeasureTemperature` from a resistance probe can be
queried alongside thermocouple-based temperatures (which are derived from voltage measurements).

# The Gate of Schwindratzeim

_Location_: Gare de péage de Schwindratzeim (48.77221, 7.60167)

_Time_: 26-08-25T18:11+2

I receive the call from Seedz, and walk on over to pick up my freshly repaired motorbike. A brief
conversation and step towards bankruptcy later, and I'm riding off to Mulhouse. I soon notice,
however, that the clutch bites a little even when fully pulled in. As I stop to investigate, I get
stuck in fourth gear on a hill. So I ride it back for them to adjust.

Weird. But nothing serious. No, say, _oil_ leaking...

So I go off again on my merry way. Finally, with the clutch repaired, I can once more enjoy the full
power of the engine.

Exuberant with this force, I arrive, in a cloud of smoke, to the gare de péage de Schwindratzeim.

There shouldn't be smoke, _yaar_.

So the customs officers stop me with concern, and I have a nice discussion about French customs as
my heart sinks, and the engine's lifeblood spills upon the motorway. To turn it back on now would be
to destroy it.

I'm stuck.

There's some hope I can just go buy a plug or something... but the wheel is covered in oil. Cleaning
it out here would be difficult, and risky.

It turns out that _would_ have been possible, maybe, though I'd have to wait till tomorrow to get a
compatible Suzuki plug.

But anyways. Some bikers show up and point out the oil on the wheel as an extreme danger. I'd rather
not risk any such things. Which means, for the first time, it's time to call roadside recovery.

So the first company I call enthusiastically agrees to come pick me up, and even says they can take
me back to Seedz.

I call them repeatedly, since they said the truck driver would call me back in about 20 minutes.

Apparently he crashed.

There's a truck driver stranded with me here for the night. I get my laptop setup, but my phones are
running low on battery. I don't have it in me to do much in the way of hacking.

<div style="text-align: center">
<img src={laptop_in_extremis} alt="My laptop left on the side of the highway." style="max-width: 70%" />
</div>

I call another recovery company. At first he agrees to come...

And then informs me that actually, he cannot, because my location counts as the highway, and he does
not have the necessary government permit.

So I call SANEF, the French highway authority, and, after a bit of time figuring out who to transfer
me to, they send over breakdown services.

The man is not very happy. And does _not_ want to ride me back all the way to Seedz. So we're going
to the depot. 

10 minute ride, 230 euro bill, and I am brusquely shown the door, since they are closing. Fair, not
exactly their fault. But not a good start to the night.

Nearest hotel is an hour's walk away. 

The rain begins to fall. 

I call an Uber. We discuss whether he knows anyone with a van that could take me and the bike back
to Seedz tomorrow morning, since the local recovery companies are charging up to 400 euros. He
might.

I arrive at the hotel.

I'm worried something other than the drain plug may be broken. I fear for the rest of my trip.

Is this defeat?

_Never give up. Never surrender._

I call up my category-theorist-biker-friend, and discuss how I may be able to perform the repair
myself.

According to him and ChatGPT, I'll need:
- A Suzuki compatible drain plug, which is apparently the somewhat special M12 × 1.25.
  Might need a larger one if the threads are stripped and that's why the plug fell out.
- The associated washer
- A rag
- Some brake cleaner to get the oil off

An alternative is to call all the local shops and see who has a van.

I steel my resolve, and, around 1 AM, fall into hypersleep, gathering energy to face the dawn.

But my dreams are dark.

# Look for me at the first light of dawn

_Location_: (the hotel)

_Time_: 2025-08-27T08:30+2

I lie there for a while, my awareness in that liminal space between conscious and subconscious, the
dawn slowly pulling me forwards, drawing out the memories behind the shapes.

And then, with a start, I sit up. I get calling.

The local mechanics might have availability, but thankfully, Seedz answers right at 9 when they
open, and confirm they can send over a repairman, and that they'll cover all the bills. Honestly,
very professional way to handle a mistake.

So we're good. Hopefully.

I walk off to get some food. Move cafes a few times, tap away at this article. Van arrives, and we
ride on over to the depot. We go ahead re-attach the drain plug

<div style="text-align: center">
<img src={drain_plug} alt="The Gladius with its drain plug re-attached" style="max-width: 50%" />
</div>

and refill the oil

<div style="text-align: center">
<img src={oil_fill} alt="Refilling the oil of the Gladius" style="max-width: 50%" />
</div>

Then we cart the bike over to a wash station, and give it a rinse

<div style="text-align: center">
<img src={wash_bike} alt="Washing spilled oil off the Gladius" style="max-width: 70%" />
</div>

Finally, we wipe off the remaining oil with brake cleaner. 

The bike is repaired, and it is time to face the Alps.

I get some supplies: power banks, cables, and something to drink. Get some Turkish food at the
excellent [Restaurant Zeugma](https://maps.app.goo.gl/c66oN3LJ9HNpkL5W8). Talk to an old man sitting
there about his time in England. Interesting guy.

<div style="text-align: center">
<img src={turkish_food} alt="Some excellent Turkish food in Strasbourg" style="max-width: 70%" />
</div>

Time drags on, I'm exhausted, and it's 19:00. I just want to rest.

But it will turn out to be very good that I did not. I set a course for Genoa.

The rain begins.

Needles.

Then bullets.

Pull over to gas station, get some coffee, and swap out my T-shirt for my armored jacket.

Now the rain begins in earnest. My visor is covered in droplets.

For long stretches, I just follow the fastest car on the road, just following the headlights.

Waze started taking me the wrong way, trying to avoid requiring a Swiss vignette, which I had
already paid for. After a few kilometers on the road to Lyon, we turn back, and switch to Google
Maps.

In the middle of the night, we cross the border with Switzerland and enter Basel.

The roads are superbly well-maintained, and empty. Winding tunnel sections. 

To be honest, it's like a racetrack the size of a country. And given the price of a vignette, versus
tolls, it's cheap too!

That's the only cheap thing in this dark place. 

I take a stop, and it's 50 CHF for a charger... and 1 CHF to use the bathroom.

Exhaustion is setting in; it's around midnight. I set course for Milan. 3 more hours.

As I speed along the massive tunnels and galleries, I feel truly proud to be human. Men, like me,
with two arms and two legs and a single mind, made these grand things.

I hope one day we will make things ever-grander, structures on the scale of stars.

Or will we simply be obsoleted?

Another tunnel. Now this is truly beautiful. I wish I stopped and took a photo.

And yet that wasn't _the_ tunnel. And now. I _will_ stop and take some photos.

<div style="text-align: center">
<img src={tunnel_bike_view} alt="The Gladius sitting in a Swiss mountain tunnel" style="max-width: 70%" />
</div>

We approach the Italian border, passport control waves me through.

The road is straight.

I may not know Italian. But my heritage speaks to me: In my genetic memory, there seems to be an
innate understanding of the beautiful language of the Italian road.

I send it.

We decelerate in Milan, at the [Idea Hotel Milano San Siro](https://sansiro.ideahotel.it/), only
three days late.

<div style="text-align: center">
<img src={milan_hotel} alt="My hotel room at the Idea Hotel Milan San Siro" style="max-width: 70%" />
</div>

It's time for hypersleep.

# Balthasar and the Storm

_Location_: Port of Genoa

One of my favorite books is _Le Périple de Baldassare_. Soon after reading it, I went to Edinburgh
on my KTM125. I came back changed.

And now, like Balthasar, I recover my heritage, and ride to Genoa. 

It's day 2. Yesterday there was an extreme weather warning, but really, last night was fine.

Today was not fine.

The rain picked up. Buffeting winds. Blinding spray.

I ride next to a truck so that its bulk protects me from the wind. We hardly go 70.

The two plastic bags around my laptop hold.

We pass between verdant mountains. I wish I had a GoPro.

The roads next to the sea turn yellow.

We arrive in Genoa. I take shelter at the gas station, and dry off my clothes under the hand dryer.

After doing my laundry, I stop at a Chinese restaurant, [Rosticeria Cinese
Ji](https://maps.app.goo.gl/o9nXde6eQVXa2Pza9). The owner doesn't speak English, I don't speak
Italian, so we manage to have a passable conversation in Mandarin, which surprises me. While I've
studied for three years, this is actually the first time I have a bona-fide organic conversation,
unable to simply swap back to English the moment the going gets tough. And it goes well! Should do
that more often.

<div style="text-align: center">
<img src={chinese_genoa} alt="The inside of Rosticeria Cinese Ji" style="max-width: 70%" />
</div>

<div style="text-align: center">
<img src={chinese_genoa_outside} alt="The sign outside Rosticeria Cinese Ji" style="max-width: 70%" />
</div>

Also, the food's good! Very reasonable prices.

We go to the ship. I thought I was early, 20:45 they said, but I am late. There's an entire horde of
bikers, very different from last time. Guess Sicily makes good biking.

We board, and, now that we're settled in, time for a bit more vibe coding.

Ship internet costs 7 euros for a GB, so we've got to get set up now that we still have data in
port.

Weirdly enough, when I tried connecting to the ship's internet, though it redirects to a login page,
Playwright downloads Chromium just fine, with some spurious warnings about TLS.

Everything else is blocked though; `ping` anything fails with 
```
From _gateway (172.20.0.1) icmp_seq=1 Destination Net Prohibited
```

Eh. Swap to data.

So last time we generated a Svelte app to go with our SQL. I started by creating a blank app using
```bash
npx sv create
```
I use `bun` as my package manager, and add support for Vitest and Playwright.

Given our prompt, based on the SQL above, Claude generated
- A file, `database.ts`, exposing some basic operations on a `wa-sqlite` database with the above
  schema; currently, just creating one
- A simple Svelte app to test and exercise this file.

Let's go over `database.ts`. It starts by defining a Typescript interface for our database:

```ts
export interface DatabaseManager {
  db: number;
  sqlite3: any;
  close(): Promise<void>;
  execute(sql: string, params?: any[]): Promise<void>;
  query(sql: string, params?: any[]): Promise<any[]>;
}
```
along with a function to create an in-memory database

```ts
/**
 * Create a new in-memory database
 */
export async function createInMemoryDatabase(): Promise<DatabaseManager> {
  const sqlite3 = await initSQLite();
  const db = await sqlite3.open_v2(':memory:');
  
  // Create schema
  await sqlite3.exec(db, SCHEMA_SQL);
  
  console.log('DB opened successfully (in-memory database)');
  
  return {
    db,
    sqlite3,
    async close() {
      await sqlite3.close(db);
    },
    async execute(sql: string, params?: any[]) {
      if (params && params.length > 0) {
        for await (const stmt of sqlite3.statements(db, sql)) {
          sqlite3.bind_collection(stmt, params);
          await sqlite3.step(stmt);
        }
      } else {
        await sqlite3.exec(db, sql);
      }
    },
    async query(sql: string, params?: any[]) {
      const results: any[] = [];
      for await (const stmt of sqlite3.statements(db, sql)) {
        if (params && params.length > 0) {
          sqlite3.bind_collection(stmt, params);
        }
        const columns = sqlite3.column_names(stmt);
        while (await sqlite3.step(stmt) === SQLite.SQLITE_ROW) {
          const row: any = {};
          columns.forEach((col, i) => {
            row[col] = sqlite3.column(stmt, i);
          });
          results.push(row);
        }
      }
      return results;
    }
  };
}
```
Claude also generated a function, `openExistingDatabase(file: File)`, to open a database stored in a
file, but right now it just does exactly the same thing, except it also opens the provided file as a
`Uint8Array` and then does nothing with it. Just caught this now as we're writing the article! So
that's fun!

Likewise, we're starting simple with the export function:
```ts
/**
 * Export database to downloadable file
 */
export async function exportDatabase(dbManager: DatabaseManager, filename: string = 'scrapebook.sqlite'): Promise<void> {
  const { db, sqlite3 } = dbManager;
  
  // For wa-sqlite, we need to serialize the database differently
  // This is a simplified version - in a real implementation you'd want
  // to use the proper VFS for file operations
  
  // For now, we'll create a simple export by dumping the schema and data
  console.log(`Export functionality not fully implemented yet for ${filename}`);
  console.log('Database would be exported here');
}
```

So I guess we're telling Claude to do import and export next.

Now, on to our Svelte app. Our `<script>` section starts by importing our database API:

```ts
import { createInMemoryDatabase, openExistingDatabase, type DatabaseManager } 
  from '$lib/database.js';
```

For state, we've got

```ts
/// An open database connection, or null if no DB is opened
let dbManager: DatabaseManager | null = null;
/// The current status of our connection as a string
let status = 'Not connected';
```

We also keep track of a file input element for imports

```ts
let fileInput: HTMLInputElement;
```

Our page is a bunch of buttons to do the obvious things:
- Create a new database
- Open an existing database
- If a database is opened (`dbManager != null`)
  - Test the open database
  - Close the open database

In code,
```svelte
<main>
  <h1>Scrapebook SPA</h1>
  <p>SQLite Database Test - First Milestone</p>
  
  <div class="status">
    <strong>Status:</strong> {status}
  </div>

  <div class="controls">
    <button on:click={createNewDatabase}>Create New In-Memory Database</button>
    
    <div class="file-input">
      <input 
        bind:this={fileInput}
        type="file" 
        accept=".sqlite,.sqlite3,.db" 
        id="file-input"
      />
      <button on:click={openFileDatabase}>Open Existing Database File</button>
    </div>
    
    {#if dbManager}
      <button on:click={testDatabase}>Test Database</button>
      <button on:click={closeDatabase}>Close Database</button>
    {/if}
  </div>

  <div class="info">
    <h2>Database Schema</h2>
    <p>The database includes the following tables:</p>
    <ul>
      <li><code>ops</code> - Operations in the pipeline graph</li>
      <li><code>op_outputs</code> - Output payloads from operations</li>
      <li><code>op_inputs</code> - Input edges between operations</li>
      <li><code>observation_sets</code> - Composite ground truth data</li>
      <li><code>artifacts</code> - Artifact store for GC/deduplication</li>
    </ul>
    
    <p><strong>Check the browser console</strong> for detailed logs about database operations.</p>
  </div>
</main>
```

And, back in `<script>` we've got functions to do each using our database API:

```ts
async function createNewDatabase() {
  try {
    // If a database is currently open, close it
    await closeDatabase();

    status = 'Creating in-memory database...';
    dbManager = await createInMemoryDatabase();
    status = 'Connected to in-memory database';
    
    // Test the database by inserting a sample record
    await testDatabase();
  } catch (error) {
    console.error('Failed to create database:', error);
    status = `Error: ${error}`;
  }
}

async function openFileDatabase() {
  const file = fileInput.files?.[0];
  if (!file) {
    alert('Please select a file first');
    return;
  }

  try {
    // If a database is currently open, close it
    await closeDatabase();

    status = `Opening database from ${file.name}...`;

    dbManager = await openExistingDatabase(file);
    status = `Connected to database: ${file.name}`;
    
    // Test the database
    await testDatabase();
  } catch (error) {
    console.error('Failed to open database:', error);
    status = `Error: ${error}`;
  }
}

async function testDatabase() {
  if (!dbManager) return;

  try {      
    // Query the ops table
    const ops = await dbManager.query('SELECT COUNT(*) as count FROM ops');
    console.log('Operations in database:', ops);
    
    // Query all table names to verify schema
    const tables = await dbManager.query(`
      SELECT name FROM sqlite_master WHERE type='table' ORDER BY name
    `);
    console.log('Tables in database:', tables);
    
  } catch (error) {
    console.error('Database test failed:', error);
  }
}

async function closeDatabase() {
  if (dbManager) {
    await dbManager.close();
    dbManager = null;
    status = 'Disconnected';
  }
}
```
We also auto-load an in-memory database on initialization
```ts
onMount(() => {
  // Auto-create in-memory database on load for demo
  createNewDatabase();
});
```
We note the generated code forgot to call `closeDatabase` before opening/creating a new one! 

Adding this makes the UI flicker a bit when we open a new DB, which is a bit irritating but eh. We
can probably change the UI to gray out the buttons rather than disappear them, and add some
interpolation[^2]. This will hopefully still work if other things affect the DB connection.

So far, so good. But, `npm run test` gives us a spurious SSR error, after all tests pass:
```
10:05:12 PM [vite] (ssr) Error when evaluating SSR module /node_modules/@sveltejs/kit/src/runtime/server/index.js: transport was disconnected, cannot call "fetchModule"
      at reviveInvokeError (file:///home/tekne/Projects/scrapebook-spa/node_modules/vite/dist/node/module-runner.js:475:14)
      at Object.invoke (file:///home/tekne/Projects/scrapebook-spa/node_modules/vite/dist/node/module-runner.js:549:11)
      at async SSRCompatModuleRunner.getModuleInformation (file:///home/tekne/Projects/scrapebook-spa/node_modules/vite/dist/node/module-runner.js:1059:7)
      at async request (file:///home/tekne/Projects/scrapebook-spa/node_modules/vite/dist/node/module-runner.js:1076:83)
      at async eval (/home/tekne/Projects/scrapebook-spa/node_modules/svelte/src/internal/client/render.js:31:1)
      at async ESModulesEvaluator.runInlinedModule (file:///home/tekne/Projects/scrapebook-spa/node_modules/vite/dist/node/module-runner.js:910:3)
      at async SSRCompatModuleRunner.directRequest (file:///home/tekne/Projects/scrapebook-spa/node_modules/vite/dist/node/module-runner.js:1119:59)
      at async SSRCompatModuleRunner.directRequest (file:///home/tekne/Projects/scrapebook-spa/node_modules/vite/dist/node/chunks/dep-Bj7gA1-0.js:18770:22)
      at async SSRCompatModuleRunner.cachedRequest (file:///home/tekne/Projects/scrapebook-spa/node_modules/vite/dist/node/module-runner.js:1037:73)
      at async eval (/home/tekne/Projects/scrapebook-spa/node_modules/svelte/src/internal/client/dev/hmr.js:7:1)
```
Turns out this is an internal Svelte issue
[(#16663)](https://github.com/sveltejs/svelte/issues/16663); this happens with default project too.
Until that gets fixed, we just change the default script in `package.json` from
```json
"scripts": {
  // -- snip
  "test": "npm run test:unit -- --run  && npm run test:e2e",
},
```
to
```json
"scripts": {
  // -- snip
  "test": "npm run test:unit && npm run test:e2e",
},
```
But now we need to press `q`. Let's see if we can get around that...
```bash
yes q | head -n1 | vitest && playwright test
```
Nope, auto-pressing `q` with `yes` too fast triggers the issue as well. 

Imagine pressing buttons manually.

I'll live.

It is a long, cold, and melancholy night. My arm hurts, sleeping on a row of three seats.

I get up. Bar's open. Get a coffee. Do a spot of writing (hi!)

<div style="text-align: center">
<img src={ferry_setup} alt="Setup inside the GNV ferry" style="max-width: 70%" />
</div>

That seat is also a _much_ better sleeping spot.

The dawn rises over the waves. 

Through the sea-spray, Palermo awaits!

[^1]: It really is amazing just how much of an impact
    [VIC173](https://artsci.calendar.utoronto.ca/course/vic173y1), the wonderfully named _Philosophy
    of Science for Physical Scientists_, had on my life. I thought, like the rest of the breadth
    courses I had to take, it was just a box-filling, essay-generating exercise, and at first it
    was. But, like, two of those readings got engraved into my mind forever.

    And [it](https://mitpress.mit.edu/9780262581691/space-from-zeno-to-einstein/) was also my first
    introduction to Kant. Though _that_ particular reading is long erased. "Ancient" thinking about
    geometry contines to baffle me.

[^2]: We can't close the database with a different function that does not set `dbManager` to `null`;
  as this creates the potential bug that if we push the test button before re-initialization is
  complete, we'll get an error, since it will attempt to call `testDatabase` on a closed DB.
  Likewise for any other DB access we may add in the future!

<script>
    import oil_spill from "$lib/assets/scraping-by/oil_spill.jpg"
    import laptop_in_extremis from "$lib/assets/scraping-by/laptop_in_extremis.jpg"
    import drain_plug from "$lib/assets/scraping-by/drain_plug.jpg"
    import oil_fill from "$lib/assets/scraping-by/oil_fill.jpg"
    import wash_bike from "$lib/assets/scraping-by/wash_bike.jpg"
    import turkish_food from "$lib/assets/scraping-by/turkish_food.jpg"
    import tunnel_bike_view from "$lib/assets/scraping-by/tunnel_bike_view.jpg"
    import milan_hotel from "$lib/assets/scraping-by/milan_hotel.jpg"
    import chinese_genoa from "$lib/assets/scraping-by/chinese_genoa.jpg"
    import chinese_genoa_outside from "$lib/assets/scraping-by/chinese_genoa_outside.jpg"
    import ferry_setup from "$lib/assets/scraping-by/ferry_setup.jpg"
</script> 
