---
title: Adventures in Type Theory 3 — Scraping By
published: '2025-08-26'
---

TFW the DB is SSA:

You’re right — good catch. The whole **point** of `artifact_slots`/`artifact_links` is to support
*GC, auditing, and provenance tooling*, not to affect the actual semantics of the SSA-like DB. The
**only semantics-critical part** is `ops` (with `input_digest` and `ground_truth_hash`),
`op_inputs`, `op_outputs`, and `composite_ground_truth`. Everything else is ancillary.

So here’s a cleaned-up **full schema** with `artifact_slots` and the `artifact_links` compatibility
views together in the **optional section at the bottom**, clearly marked as “non-semantic /
droppable.”

---

```sql
PRAGMA journal_mode = WAL;

/* =======================
   ARTIFACTS (content-addressed bytes)
   ======================= */
CREATE TABLE IF NOT EXISTS artifacts (
  artifact_hash  BLOB PRIMARY KEY,   -- 32B sha256(bytes)
  bytes          BLOB                -- payload (nullable; can be purged)
);

CREATE VIEW IF NOT EXISTS artifact_sizes AS
SELECT artifact_hash, length(bytes) AS size_bytes FROM artifacts;


/* =======================
   OPS (Transform / Analysis / Observation)
   =======================

Classes:
  Transform   : is_observation = 0 AND op_key = input_digest
  Analysis    : is_observation = 0 AND op_key != input_digest
  Observation : is_observation = 1 AND op_key != input_digest

input_digest (32B; computed in app):
  sha256( op_type || 0x00 || tool_id || 0x00 || canon(params_json) || 0x00 ||
          concat(h_i) )
where h_i are the artifact hashes from artifact_slots with idx < 0 (inputs),
ordered by idx ASC (i.e., -1,-2,-3 → input slots 0,1,2) and including multiplicity.

Ground-truth algorithm:
  as described in docs — collect inputs’ ground truths + self if observation,
  dedupe, expand composites, dedupe again, then NULL/single/composite hash.
*/
CREATE TABLE IF NOT EXISTS ops (
  op_key            BLOB PRIMARY KEY,   -- 32B unique key (random for run-addressed)
  op_type           TEXT NOT NULL,      -- e.g. 'http_fetch','html_to_text','llm_infer','human_label'
  tool_id           TEXT NOT NULL,      -- e.g. 'requests_v1','bs4_v1','rules_v2'
  params_json       TEXT,               -- canonical JSON (sorted keys, stable forms)

  input_digest      BLOB NOT NULL,      -- 32B

  is_observation    INTEGER NOT NULL DEFAULT 0 CHECK (is_observation IN (0,1)),
  observed_at       TEXT,               -- optional clock; MUST be NULL if not observation

  ground_truth_hash BLOB,               -- 32B per algorithm above (may be NULL only if synthetic)

  -- Validity checks
  CHECK ( is_observation = 0 OR op_key != input_digest ),
  CHECK ( (is_observation = 1) OR (observed_at IS NULL) ),
  CHECK ( (is_observation = 1 AND ground_truth_hash IS NOT NULL) OR (is_observation = 0) )
);

-- Indexes
CREATE INDEX IF NOT EXISTS idx_ops_observed_at_obs ON ops(observed_at) WHERE is_observation = 1;
CREATE INDEX IF NOT EXISTS idx_ops_ground_truth    ON ops(ground_truth_hash);
CREATE INDEX IF NOT EXISTS idx_ops_type            ON ops(op_type);
CREATE INDEX IF NOT EXISTS idx_ops_inputdig        ON ops(input_digest);


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
  producer_op_key     BLOB NOT NULL,     -- producing op
  producer_output_idx INTEGER NOT NULL,  -- producing output slot
  PRIMARY KEY (op_key, idx)
);

CREATE INDEX IF NOT EXISTS idx_op_inputs_producer ON op_inputs(producer_op_key, producer_output_idx);


/* =======================
   COMPOSITE GROUND TRUTH (hash → sorted members)
   ======================= */
CREATE TABLE IF NOT EXISTS composite_ground_truth (
  composite_hash  BLOB PRIMARY KEY,  -- 32B
  members_blob    BLOB NOT NULL      -- 32*n bytes (n >= 2)
);

CREATE INDEX IF NOT EXISTS idx_cgt_members_len ON composite_ground_truth(length(members_blob));


/* =======================
   VIEWS (convenience)
   ======================= */

-- Classify each op
CREATE VIEW IF NOT EXISTS v_ops_class AS
SELECT
  o.*,
  CASE
    WHEN o.is_observation = 0 AND o.op_key = o.input_digest THEN 'transform'
    WHEN o.is_observation = 1 THEN 'observation'
    ELSE 'analysis'
  END AS op_class
FROM ops o;

-- Ground truth kind
CREATE VIEW IF NOT EXISTS v_ops_ground_kind AS
SELECT
  o.*,
  CASE
    WHEN o.ground_truth_hash IS NULL THEN 'synthetic'
    WHEN EXISTS (SELECT 1 FROM ops x WHERE x.op_key = o.ground_truth_hash)
         THEN 'single_origin'
    WHEN EXISTS (SELECT 1 FROM composite_ground_truth c WHERE c.composite_hash = o.ground_truth_hash)
         THEN 'composite_origin'
    ELSE 'unknown_single'
  END AS ground_kind
FROM ops o;

-- Inputs resolved with producer outputs
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


/* ==========================================================
   OPTIONAL / NON-SEMANTIC SECTION (GC, provenance, audits)
   ----------------------------------------------------------
   These tables/views can be DROPPED without affecting the
   semantics of ops / input_digest / ground truth.
   ========================================================== */

-- Artifact slots: per-slot linkage (signed idx)
CREATE TABLE IF NOT EXISTS artifact_slots (
  artifact_hash  BLOB NOT NULL,   -- 32B
  op_key         BLOB NOT NULL,
  idx            INTEGER NOT NULL,  -- input s → -(s+1); output s → s
  PRIMARY KEY (artifact_hash, op_key, idx)
);

CREATE INDEX IF NOT EXISTS idx_slots_op_in     ON artifact_slots(op_key, idx) WHERE idx < 0;
CREATE INDEX IF NOT EXISTS idx_slots_op_out    ON artifact_slots(op_key, idx) WHERE idx >= 0;
CREATE INDEX IF NOT EXISTS idx_slots_artifact  ON artifact_slots(artifact_hash);

-- Input/output decoded views
CREATE VIEW IF NOT EXISTS v_artifact_inputs AS
SELECT op_key, (-idx - 1) AS slot_idx, artifact_hash
FROM artifact_slots WHERE idx < 0;

CREATE VIEW IF NOT EXISTS v_artifact_outputs AS
SELECT op_key, idx AS slot_idx, artifact_hash
FROM artifact_slots WHERE idx >= 0;

-- Role summary per op/artifact
CREATE VIEW IF NOT EXISTS v_artifact_roles AS
WITH flags AS (
  SELECT op_key, artifact_hash,
         MAX(CASE WHEN idx < 0 THEN 1 ELSE 0 END) AS has_input,
         MAX(CASE WHEN idx >= 0 THEN 1 ELSE 0 END) AS has_output
  FROM artifact_slots
  GROUP BY op_key, artifact_hash
)
SELECT *, (has_input + has_output*2) AS role_mask
FROM flags;

-- artifact_links compatibility (drop-in, GC-oriented)
CREATE VIEW IF NOT EXISTS artifact_links_consumed AS
SELECT s.op_key, 'consumed' AS direction, (-s.idx - 1) AS slot_idx, s.artifact_hash
FROM artifact_slots s WHERE s.idx < 0;

CREATE VIEW IF NOT EXISTS artifact_links_produced AS
SELECT s.op_key, 'produced' AS direction, s.idx AS slot_idx, s.artifact_hash
FROM artifact_slots s WHERE s.idx >= 0;

CREATE VIEW IF NOT EXISTS artifact_links AS
SELECT * FROM artifact_links_consumed
UNION ALL
SELECT * FROM artifact_links_produced;

-- GC helpers
CREATE VIEW IF NOT EXISTS v_live_artifacts AS
SELECT DISTINCT artifact_hash FROM artifact_slots;

-- Referenced artifacts that have NO row in `artifacts` (broken reference)
CREATE VIEW IF NOT EXISTS v_missing_artifacts AS
SELECT DISTINCT s.artifact_hash
FROM artifact_slots s
LEFT JOIN artifacts a USING (artifact_hash)
WHERE a.artifact_hash IS NULL;

-- Referenced artifacts that HAVE a row but payload is purged (bytes IS NULL)
CREATE VIEW IF NOT EXISTS v_purged_artifacts AS
SELECT DISTINCT s.artifact_hash
FROM artifact_slots s
JOIN artifacts a USING (artifact_hash)
WHERE a.bytes IS NULL;

-- Referenced artifacts that are either missing OR purged
CREATE VIEW IF NOT EXISTS v_missing_or_purged_artifacts AS
SELECT DISTINCT s.artifact_hash
FROM artifact_slots s
LEFT JOIN artifacts a USING (artifact_hash)
WHERE a.artifact_hash IS NULL OR a.bytes IS NULL;

-- (Optional) One-stop status view (OK / purged_bytes / missing_row)
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

---

✅ Now `artifact_slots` and `artifact_links` are clearly **non-semantic / optional**, all the way at
the bottom, safe to drop. Do you want me to also give you a **toy insertion script** (one
observation → one transform → one analysis) that exercises these tables and shows the ground-truth
chain?
