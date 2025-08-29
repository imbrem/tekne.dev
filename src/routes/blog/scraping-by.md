---
title: Adventures in Type Theory 3 — Scraping By
published: '2025-08-27'
---

_Location_: [Boulangerie aux délices de Souffel](https://maps.app.goo.gl/2vb9qMHP9eSuZTTr6)
(42.62627, 7.72929)

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

A cloud of white smoke catches up to me as I pull to a stop. There's oil everywhere, and my rear
wheel is completely soaked.

<!-- <div style="text-align: center">
<img src={oil_spill} alt="The Gladius missing its drain plug" style="max-width: 70%" />
</div> -->

And that’s how I learned that French customs, perhaps uniquely in the world, are empowered to
conduct searches anywhere in the country, not just at the border.

Van's here, yo.

# A Chat at the Pâtisserie

_Location_: Boulangerie Pâtisserie Berg Woustviller
_Time_: 2025-08-26T15:30+2

I've spent a solid chunk of my youth thinking about _scraping_. If I ever see a paper copy of the
newspaper _Miliyet_, I think I'll cry.

Thanks to the influence of a certain Professor Berkovitz[^1], I know just enough about the
philosophy of science to be dangerous. I promise these are related. Maybe.

Today we're meditating on an SQL schema for observations on the world, analyses of those
observations, and transformations on the resulting data. In particular, everything in this section
really is a half-baked meditation for a project I'm working on: I hardly know SQL!

The concrete application here is scraping:
- The _observations_ are opening a page, and seeing what HTML response comes flying back
- The _transformation_ would be, for example, scraping out the plain-text using a set of
  deterministic rules
- The _analysis_ might be using or training a machine-learning model, or asking a human annotator to
  determine ~something~ about our (potentially transformed) data.
- And we might further _transform_s the analysis, by, for example, computing a mean, or taking the
  output of our machine learning model and graphing sentiment.

So, a basic schema might look like
```sql
-- TODO: this
DROP TABLE
```

- We're using the usual relational pattern for multiple inputs and outputs
- Every observation, analysis, and transformation has a unique GUID, so we can just merge SQLite
  files from different databases
- The _input_ to every operation is a vector of outputs from other operations, plus parameters

Now, this framework is perfectly generic. For example, consider a scientific experiment:
- We make an _observation_ by recording direct sensor data, say the resistance of a temperature
  probe
- We _transform_ it into whatever we want to measure using our calibration data, here this would be
  the temperature
- We _analyze_ our transformed observations in a potentially nondeterminisitc way to get our
  results, perhaps by fitting a linear regression between temperature and the speed of a chemical
  reaction.

So for our scraping example, we might have
- An operation `fetch_http` with the URL and some user-agent nonsense as parameters, and the
  resulting HTTP headers and returned data as results 1 and 2 respectively. This is an
  _observation_.
- An operation `extract_text_from_html` consuming the HTML from result 2 and returning the resulting
  text as its only result. If deterministic, this is a _transformation_, so, e.g., would be
  deduplicated w.r.t. the inputs.
- An operation `split_text_into_sentences` consuming the text and returning a list of sentences.
  Parameters might include language information. This is also, usually, a transformation, unless
  maybe ML is used.
- An operation `embed_sentences` consuming the list of sentences and returning a list of embeddings,
  e.g. using `SentenceTransformers`. Can be either an analysis or transformation; I'd go with
  transformation since we want to cache the outputs.
- An analysis might be manually labelling a random subset of the sentences; note that even just
  selecting a random subset would count as an analysis, since we can't cache it based on just the
  input.

  Unless we're studying the human labelling pattern itself, though, it's _not_ an observation!

Since transformations are _pure_, we'd like to deduplicate them so that two equal transformations
with the same inputs have the same output. We can do this by adding a field `input_digest`. Then
we'll require that the ID of a transformation is always just the input digest!
```sql
-- TODO: this
DROP TABLE
```
In general, we want to index on our input digest, so that we can, e.g., query for all observations
of a given thing, even if each has a unique ID (being an observation rather than a transformation):
```sql
--TODO: this
DROP TABLE
```

While we're at this deduplication business, we'd like to add an additional table to store cached
data, so as to be able to deduplicate the results of operations, as well as make versions of the DB
which don't store intermediate results to save space and bandwidth:
```sql
--TODO: this
DROP TABLE
```

Note that we _don't_ change the output of operations to be a potential hash of cached data. It's
still just data, which might contain hashes. If you want to return cached data, just return its
hash, and of course stick the data in the cache.

Of course, if we want to do garbage collection, we need to keep track of which hashes are referenced
by which operations, so we can add a table and some views
```sql
--TODO: this
DROP TABLE
```
But this does not actually affect the semantics of our DB so far outside of GC.

Now, another thing we want to do is, given any operation, quickly figure out its _ground truth_: the
set of observations on which it is based. For a single observation, we can just add a
`ground_truth_hash` field to our schema:
```sql
--TODO: this
DROP TABLE
```
For _multiple_ observations, however, we need some kind of way of keeping track of the _set_ of
observations we're working with. We could:
- Have a separate ground truth table containing records `(operation, observation)`, but the size of
  this table can, in the worst case, grow quadratically with the number of operations
- Have a separate table defining _sets_ of ground truth observations, given by their hashes

Let's go with the latter
```sql
--TODO: this
DROP TABLE
```

Here's a view to compute which observations depend on an observation (_including_ the observation
itself):
```sql
--TODO: this
DROP TABLE
```

We'll have the convention that: 
- the set `{observation_id}` is just represented as the observation ID
- the set `∅` is represented as `NULL`

We'll have the further convention that an operation _encapsulates_ it's sub-operations; i.e., the
ground truth of an observation `id` is `{id}`, regardless of what operations appear in its inputs.
For a non-observation, we define 
```math
\mathsf{ground}(o) = \bigcup_{(i, j) ∈ \mathsf{inputs}(o)}\mathsf{ground}(i)
```
It's up to user-code to compute the appropriate hash and, if necessary, update the
`observation_sets` table. So notice we end up with SQL

```sql
--TODO: this
DROP TABLE
```

So we can just drop the `op_kind` field and replace it with views:
```sql
--TODO: this
DROP TABLE
```

Speaking of encapsulation; the final bit of functionality we want is to encapsulate compositions of
transformations, analyses, and operations. 

That is, you might notice that our definition of observation above is very direct: it's the raw
sensor data. _Most_ of the time, however, you'd consider the transformed data the observation.
Especially since the "raw" sensor data is a somewhat arbitrary concept, and even if defined may not
be accessible; consider a lab instrument which is calibrated at the factory and displays some
number, which the internal electronics has computed from raw sensor inputs inaccessible from the
external interface. Moreover, you often don't care about the raw data, so long as the output is
well-calibrated; you want to abstract away over _how_ exactly things are measured.

Let's start with composing transformations. Say we define
```
ComplexOp(A, B, C) := SimpleOp(SimpleOp2(A, B), C)
```
Note I'm writing `OperationResult(Inputs)` here, to make each operation's inputs clear. So, for
example, `SimpleOp` and `SimpleOp2` might both be invocations of the same `simple_op`. Here, `A, B,
C` can be anything, and in particular observations. But, if `SimpleOp` and `SimpleOp2` are
transformations, we want `ComplexOp` to be a transformation as well!

A simple solution is to add an `alias` field to our schema, and say that `ComplexOp` has inputs
`A, B, C` and _aliases_ `SimpleOp`. Then `ComplexOp` is a transformation iff all dependencies of
`ComplexOp` which are not also dependencies of `A, B, C` are transformations.

And, of course, if we specify the inclusions
```
Transformations ⊆ Analyses ⊆ Observations
```
then we want to say the same about analyses and observations. And this gives us the expected results
for compound measurements; for example,
```
MeasureTemperature() := ComputeTemperature(MeasureResistance(), GetCalibration())
```
And, if we want to, we can always _discard_ the alias data to save space. So we can encapsulate
complex measurements with simple ones.

And we can do the same, e.g., with a machine-learning pipeline:
```
(TestData(InputData), TrainData(InputData)) := TrainTestSplit(InputData)
TrainModel(InputData) := TrainNN(NormalizeData(TrainData(InputData), SampleRandomWeights()))
TestModel(InputData) := TestNN(TrainModel(InputData), NormalizeData2(TestData(InputData)))
```
Here,
- `TrainTestSplit` is an _analysis_, since it's making a nondeterministic choice of split. Of
  course, we _could_ make it a transformation with the seed as its parameter, but that's just
  storing an analysis in a more compressed way. Conceptually, it's an analysis.

  `TestData` and `TrainData` would be outputs 0 and 1
- `NormalizeData` is a _transformation, as would `NormalizeData2`.
- `SampleRandomWeights` is an analysis as well
- `TrainNN` would usually be an analysis if the gradient descent used is nondeterministic
- `TestNN` would usually be a transformation

So, we implement this by simply having an `alias` field:

```sql
--TODO: this
DROP TABLE
```

This leaves us with our final schema:
```sql
--TODO: this
DROP TABLE
```

# The Gate of Schwindratzeim

_Location_: Gare de péage de Schwindratzeim

_Time_: TODO this

- I ride off on my freshly repaired motorbike

- The clutch bites a little even when fully pulled in, I find myself stuck-ish on a hill

- So I ride it back. Weird (TM). They adjust it and send me on my merry way.

- I begin the ride to Mulhouse

- Reach the payment gate

- Oiled up

- ...

<!-- # GPTisms

TFW the DB is SSA:

You’re right — good catch. The whole **point** of `artifact_slots`/`artifact_links` is to support
*GC, auditing, and provenance tooling*, not to affect the actual semantics of the SSA-like DB. The
**only semantics-critical part** is `ops` (with `input_digest` and `ground_truth_hash`),
`op_inputs`, `op_outputs`, and `composite_ground_truth`. Everything else is ancillary.

So here’s a cleaned-up **full schema** with `artifact_slots` and the `artifact_links` compatibility
views together in the **optional section at the bottom**, clearly marked as “non-semantic /
droppable.”

Got it ✅ — here’s the final cleaned-up schema with your two last changes:

1. **Input digest computation doc**: now explicitly says `h_i` are the **raw bytes** from each input (in order, catenated), not hashes.
2. **Alias validity note**: clarified in the docs that alias encapsulation has constraints on what can appear inside, depending on whether the alias is itself an observation or analysis. These are **application-level invariants**, not enforced in SQL.

---

```sql
PRAGMA journal_mode = WAL;

/* =============================================================================
   SCRAPEBOOK / OBSERVATION DB — SEMANTICS-FIRST SCHEMA
   -----------------------------------------------------------------------------
   Core model
   • ops: every execution node (transform / analysis / observation).
     An op may also be an *alias* (structural), but aliasing is orthogonal to class.
   • op_inputs: wire consumer input slots to producer output slots.
   • op_outputs: payload bytes per producer output slot (0..n-1).
   • composite_ground_truth: content-addressed sets for multi-origin ground truths.
   • artifacts: optional content-addressed byte store (useful for GC/dedupe).
   -----------------------------------------------------------------------------
   Classes (derived; see v_ops_class):
     - Transform   : op_key = input_digest
     - Observation : ground_truth = op_key
     - Analysis    : otherwise

   Aliases (orthogonal, materialized)
     - alias (nullable) points to an underlying op you’re encapsulating.
     - When creating an alias op A of target T:
         1) Set A.alias = T.op_key
         2) Copy T’s op_outputs into A (same indices, same data)
         3) Usually set A.ground_truth = T.ground_truth,
            unless A is an observational “box” (then ground_truth = A.op_key).
     - Purpose: encapsulate a subgraph (e.g. pipeline) behind a higher-level
       operation, so you can safely drop or omit the inner subgraph when summarizing/exporting.

     Application-level constraints (not enforced in SQL):
       * If the alias op is NOT an observation, then none of its encapsulated
         inner ops may be observations, except those depending directly on the
         alias’s external inputs.
       * If the alias op is NOT an observation or analysis, then none of its
         encapsulated inner ops may be analyses, except those depending directly
         on the alias’s external inputs.
       Example:
         ComplexOp(A,B,C) aliases SimpleOp(SimpleOp2(A,B), C).
         - A, B, C are unconstrained.
         - If ComplexOp is not an observation, then neither SimpleOp nor
           SimpleOp2 may be observations.
         - If ComplexOp is a transform, then neither SimpleOp nor SimpleOp2
           may be analyses or observations.

   Ground truth (app-side)
     • Observation: ground_truth := op_key (early return).
     • Otherwise:
         L := [non-NULL ground_truths of input producers]
         sort & dedupe → expand any composite members → sort & dedupe
         → NULL / single / composite (insert composite row if new)

   Input digest (app-side)
     • input_digest := sha256(op_type || 0x00 || tool_id || 0x00 ||
                              canon(params_json) || 0x00 ||
                              concat(h_i))
     • Here h_i are the **raw input bytes**, concatenated in input-slot order
       (multiplicity preserved), not hashes. This makes transforms content-defined.
   ============================================================================= */


/* =======================
   ARTIFACTS (content-addressed bytes)
   ======================= */
CREATE TABLE IF NOT EXISTS artifacts (
  artifact_hash  BLOB PRIMARY KEY,   -- 32B sha256(bytes)
  bytes          BLOB                -- payload; may be NULL (purged)
);

CREATE VIEW IF NOT EXISTS artifact_sizes AS
SELECT artifact_hash, length(bytes) AS size_bytes FROM artifacts;


/* =======================
   OPS (Transform / Analysis / Observation; alias is orthogonal)
   ======================= */
CREATE TABLE IF NOT EXISTS ops (
  op_key        BLOB PRIMARY KEY,   -- 32B unique key (random for run-addressed)
  op_type       TEXT NOT NULL,      -- e.g. 'http_fetch','html_to_text','llm_infer','human_label'
  tool_id       TEXT NOT NULL,      -- e.g. 'requests_v1','bs4_v1','rules_v2'
  params_json   TEXT,               -- canonical JSON (sorted keys, stable forms)

  input_digest  BLOB NOT NULL,      -- 32B

  ground_truth  BLOB,               -- 32B; NULL only if synthetic / no provenance
  observed_at   TEXT,               -- optional wall clock; MUST be NULL unless observation

  alias         BLOB,               -- nullable: op_key this row *encapsulates* (outputs copied)

  CHECK ( (observed_at IS NULL) OR (ground_truth = op_key) )
);

-- Helpful indexes
CREATE INDEX IF NOT EXISTS idx_ops_ground_truth ON ops(ground_truth);
CREATE INDEX IF NOT EXISTS idx_ops_type         ON ops(op_type);
CREATE INDEX IF NOT EXISTS idx_ops_inputdig     ON ops(input_digest);
CREATE INDEX IF NOT EXISTS idx_ops_alias        ON ops(alias);
CREATE INDEX IF NOT EXISTS idx_ops_observed_at  ON ops(observed_at) WHERE ground_truth = op_key;


/* =======================
   OP OUTPUTS (payloads, app-defined)
   ======================= */
CREATE TABLE IF NOT EXISTS op_outputs (
  op_key  BLOB NOT NULL,     -- producing op
  idx     INTEGER NOT NULL,  -- output slot: 0,1,2,...
  data    BLOB,              -- arbitrary bytes; may be NULL
  PRIMARY KEY (op_key, idx)
);


/* =======================
   OP INPUTS (structural edges)
   ======================= */
CREATE TABLE IF NOT EXISTS op_inputs (
  op_key              BLOB NOT NULL,     -- consumer op
  idx                 INTEGER NOT NULL,  -- consumer input slot (0,1,2,...)
  producer_op_key     BLOB NOT NULL,     -- producing op (may itself be an alias)
  producer_output_idx INTEGER NOT NULL,  -- producing output slot
  PRIMARY KEY (op_key, idx)
);

CREATE INDEX IF NOT EXISTS idx_op_inputs_producer ON op_inputs(producer_op_key, producer_output_idx);


/* =======================
   COMPOSITE GROUND TRUTH (hash → sorted members)
   ======================= */
CREATE TABLE IF NOT EXISTS composite_ground_truth (
  composite_hash  BLOB PRIMARY KEY,  -- 32B
  members_blob    BLOB NOT NULL      -- 32*n bytes (n >= 2), members in ascending byte order
);

CREATE INDEX IF NOT EXISTS idx_cgt_members_len ON composite_ground_truth(length(members_blob));


/* =======================
   VIEWS (summaries)
   ======================= */

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

-- Ground truth kind
CREATE VIEW IF NOT EXISTS v_ops_ground_kind AS
SELECT
  o.*,
  CASE
    WHEN o.ground_truth IS NULL THEN 'synthetic'
    WHEN EXISTS (SELECT 1 FROM ops x WHERE x.op_key = o.ground_truth)
         THEN 'single_origin'
    WHEN EXISTS (SELECT 1 FROM composite_ground_truth c WHERE c.composite_hash = o.ground_truth)
         THEN 'composite_origin'
    ELSE 'unknown_single'
  END AS ground_kind
FROM ops o;

-- Consumer inputs joined to producer outputs (aliases work since outputs are copied)
CREATE VIEW IF NOT EXISTS v_inputs_resolved AS
SELECT
  i.op_key           AS consumer_op,
  i.idx              AS consumer_idx,
  i.producer_op_key,
  i.producer_output_idx,
  o.data             AS producer_output_data
FROM op_inputs i
JOIN op_outputs o
  ON o.op_key = i.producer_op_key
 AND o.idx    = i.producer_output_idx;


/* =============================================================================
   OPTIONAL / NON-SEMANTIC SECTION (GC, provenance, audits)
   ============================================================================= */

-- Per-slot artifact linkage (signed indices)
--   input slot s → idx = -(s+1); output slot s → idx = s
CREATE TABLE IF NOT EXISTS artifact_slots (
  artifact_hash  BLOB NOT NULL,   -- 32B
  op_key         BLOB NOT NULL,
  idx            INTEGER NOT NULL,
  PRIMARY KEY (artifact_hash, op_key, idx)
);

CREATE INDEX IF NOT EXISTS idx_slots_op_in     ON artifact_slots(op_key, idx) WHERE idx < 0;
CREATE INDEX IF NOT EXISTS idx_slots_op_out    ON artifact_slots(op_key, idx) WHERE idx >= 0;
CREATE INDEX IF NOT EXISTS idx_slots_artifact  ON artifact_slots(artifact_hash);

-- Decoded conveniences
CREATE VIEW IF NOT EXISTS v_artifact_inputs AS
SELECT op_key, (-idx - 1) AS slot_idx, artifact_hash
FROM artifact_slots WHERE idx < 0;

CREATE VIEW IF NOT EXISTS v_artifact_outputs AS
SELECT op_key, idx AS slot_idx, artifact_hash
FROM artifact_slots WHERE idx >= 0;

-- Old-style links (for GC tools that expect "consumed/produced")
CREATE VIEW IF NOT EXISTS artifact_links_consumed AS
SELECT s.op_key, 'consumed' AS direction, (-s.idx - 1) AS slot_idx, s.artifact_hash
FROM artifact_slots s WHERE idx < 0;

CREATE VIEW IF NOT EXISTS artifact_links_produced AS
SELECT s.op_key, 'produced' AS direction, s.idx AS slot_idx, s.artifact_hash
FROM artifact_slots s WHERE idx >= 0;

CREATE VIEW IF NOT EXISTS artifact_links AS
SELECT * FROM artifact_links_consumed
UNION ALL
SELECT * FROM artifact_links_produced;

-- GC helpers
CREATE VIEW IF NOT EXISTS v_live_artifacts AS
SELECT DISTINCT artifact_hash FROM artifact_slots;

CREATE VIEW IF NOT EXISTS v_missing_artifacts AS
SELECT DISTINCT s.artifact_hash
FROM artifact_slots s
LEFT JOIN artifacts a USING (artifact_hash)
WHERE a.artifact_hash IS NULL;

CREATE VIEW IF NOT EXISTS v_purged_artifacts AS
SELECT DISTINCT s.artifact_hash
FROM artifact_slots s
JOIN artifacts a USING (artifact_hash)
WHERE a.bytes IS NULL;

CREATE VIEW IF NOT EXISTS v_missing_or_purged_artifacts AS
SELECT DISTINCT s.artifact_hash
FROM artifact_slots s
LEFT JOIN artifacts a USING (artifact_hash)
WHERE a.artifact_hash IS NULL OR a.bytes IS NULL;

CREATE VIEW IF NOT EXISTS v_artifact_health AS
SELECT
  s.artifact_hash,
  CASE
    WHEN a.artifact_hash IS NULL THEN 'missing_row'
    WHEN a.bytes IS NULL          THEN 'purged_bytes'
    ELSE 'ok'
  END AS status
FROM artifact_slots s
LEFT JOIN artifacts a USING (artifact_hash)
GROUP BY s.artifact_hash;
```

--- -->

Would you like me to also give you a **worked example insertion script** (e.g. `ComplexOp(A,B,C)` aliasing `SimpleOp(SimpleOp2(A,B),C)`) that shows exactly how to populate `ops`, `op_inputs`, `op_outputs` under these rules?

[^1]: It really is amazing just how much of an impact VIC172 had on my life. I thought, like the
    rest of the breadth courses I had to take, it was just a box-filling, essay-generating exercise,
    and at first it was. But, like, two of those readings got engraved into my mind forever.

    And it was also my first introduction to Kant. Though _that_ particular reading is long erased.
    "Ancient" thinking about geometry contines to baffle me.

<!-- 
<script>
    import oil_spill from "$lib/assets/scraping-by/oil-spill.jpg"
</script> -->
