# CLAUDE.md

## Project Overview

Personal website and blog for Jad Ghalayini (tekne.dev). Static site built with SvelteKit, deployed to Firebase Hosting.

## Commands

**Package manager is pnpm.** There is a Nix dev shell (`nix develop`, or `direnv allow` via `.envrc`) providing Node 24, pnpm, and `firebase-tools`. The tests need `firebase` on PATH, so run them inside the shell.

- `pnpm dev` — Start dev server
- `pnpm build` — Build static site to `build/`
- `pnpm test` — Build, then run the CAS and hosting suites
- `pnpm test:cas` — CAS invariants only; pure and fast, no build or server
- `pnpm preview` — Preview production build (**Vite, not Firebase** — see below)
- `pnpm check` — Type-check with svelte-check
- `pnpm lint` / `pnpm format` — Prettier + ESLint
- `pnpm cas -- <add|ls|verify|check|aliases>` — Manage the content-addressed store
- `firebase emulators:start --only hosting` — Serve `build/` under the real hosting rules
- `firebase deploy` — Deploy to Firebase Hosting

pnpm's strict `node_modules` is deliberate: it caught `vite-imagetools` being imported by `Img.svelte` while only present as a hoisted transitive dependency. Anything imported must be declared. Dependency install scripts are blocked by default and an unapproved one is a hard error — `pnpm-workspace.yaml` allows `sharp`, which backs `@sveltejs/enhanced-img`.

### Tests

`tests/cas.test.mjs` asserts the store's invariants — every object hashes to its own name, objects carry no extension, names resolve, history never references a dropped object.

`tests/hosting.test.mjs` runs the **real Firebase hosting emulator** and asserts status codes and served bytes. This is the layer `pnpm preview` cannot reach, and the reason it exists is in the file header: the site once served HTTP 404 and an empty shell for every extensionless URL, for about a year, while looking perfect in a browser. So the assertions check the status code and the actual response body, never "does the page look right".

Note the emulator does not implement range requests (returns 200 where production returns 206), so range behaviour — which is what makes range-querying a stored SQLite database viable — can only be confirmed against the deployed site.

## Architecture

### Framework

SvelteKit 5 with `@sveltejs/adapter-static` for static site generation. All pages are prerendered.

### Key Directories

```
src/
├── app.html                     # HTML shell (Google Analytics, KaTeX CDN)
├── content/blog/                # Blog post markdown, grouped by series
│   ├── adventures-in-type-theory/
│   └── old/                     # Pre-series posts (served at /blog/<slug>)
├── lib/
│   ├── assets/                  # Images, one subdirectory per blog post
│   ├── components/
│   │   ├── Header.svelte        # Navigation header
│   │   └── Img.svelte           # enhanced:img wrapper, optional <figcaption>
│   ├── config.ts                # Site config (title, author, URLs)
│   ├── icons/                   # SVG icon components (Home, Github, Gitlab, Mail)
│   ├── styles/style.css         # Global styles (dark theme, Fira Code font)
│   └── utils/index.ts           # fetchMarkdownPosts(), buildPostLookup()
├── routes/
│   ├── +layout.svelte           # Root layout
│   ├── +layout.ts               # prerender = true
│   ├── +page.svelte             # Home page (bio, publications)
│   ├── api/posts/+server.ts     # JSON API returning sorted blog posts
│   ├── rss.xml/+server.ts       # RSS feed
│   ├── sitemap.xml/+server.ts   # Sitemap
│   └── blog/
│       ├── +page.svelte         # Blog index
│       ├── +page.ts             # Fetches from /api/posts
│       └── [...slug]/           # Catch-all post route (resolves via lookup table)
static/
├── favicon.png
└── ert.pdf
```

### Blog System

Blog posts are `.md` files under `src/content/blog/`, **not** under `src/routes/`. They use MDsveX (markdown preprocessed as Svelte components) with frontmatter metadata:

```yaml
---
title: Post Title
published: 'YYYY-MM-DD'
edited: 'YYYY-MM-DD' # optional
description: One-line summary for RSS, sitemap, and the blog index
categories: [type-theory, lean] # optional
series: Adventures in Type Theory # optional
uuid: <stable uuid, never change once published>
aliases: [old-url-slug] # optional extra URLs that resolve to this post
---
```

A post's directory determines its canonical URL: `src/content/blog/<series-dir>/<slug>.md` is served at `/blog/<series-dir>/<slug>`, except for `old/`, which is served at `/blog/<slug>` to preserve pre-restructure URLs.

Posts are auto-discovered via `import.meta.glob('/src/content/blog/**/*.md')`. Two utilities consume that glob:

- `fetchMarkdownPosts()` — flat list of posts with metadata, backing `/api/posts` (sorted by publish date), the blog index, RSS, and the sitemap.
- `buildPostLookup()` — the `[...slug]` route's resolution table. Each post is registered under **several** keys, all of which resolve to it: canonical path, bare slug (legacy pre-restructure URL), `uuid`, and any `aliases`. `entries()` prerenders one page per key, so old links keep working.

Because URLs are derived from filenames, **moving or renaming a published post breaks its URL** — add the old slug to `aliases` when you do.

### Markdown Features

- **Code highlighting**: Shiki with Nord theme. Languages are preloaded in `svelte.config.js`; add any new language to that list.
- **Math**: LaTeX via remark-math + rehype-katex-svelte
- **Footnotes**: remark-footnotes
- **Images**: `@sveltejs/enhanced-img`. In a post, import with `?enhanced` inside a `<script module>` block and render via `$lib/components/Img.svelte`.

Mermaid is **not** available: the dependency was removed and nothing ever initialized it client-side. `svelte.config.js` still special-cases a `mermaid` fence into `<pre class="mermaid">`, but no code renders that, so a mermaid fence will come out as unstyled text.

### Styling

- Dark theme (#222222 background)
- Fira Code monospace font
- Cyan accent color for links/hover
- Responsive layout with 77rem max-width

### Content-addressed store (`/cas/`)

The store holds **bytes, keyed only by BLAKE3 hash**: `static/cas/<hash>` served
at `/cas/<hash>`. No extension, no media type, no filename — `/cas/<hash>` means
"give me these bytes" and nothing more. Objects are committed to the repo, so the
repository _is_ the store: nothing generates it, so nothing can drift from it,
and `pnpm preview` serves exactly what deploys.

Everything else — media type, download filename, title — belongs to a **name**,
not to the object. `scripts/cas.mjs` manages both:

- `pnpm cas -- add <file> [--name <alias>]... [--title <t>]` — store and name
- `pnpm cas -- ls` — list objects, current names, retired bindings
- `pnpm cas -- verify` — re-hash every object; asserts the store's invariant
- `pnpm cas -- check` — assert `firebase.json` agrees with `cas.json`
- `pnpm cas -- aliases` — print the hosting entries `check` expects

The manifest is `static/cas.json` (served at `/cas.json`): immutable `objects`,
mutable `names` carrying the semantics, and a `history` of every retired
name→hash binding with dates — the seed of a publication-history table.

Four things here are deliberate and easy to break:

- **Objects are bare hashes.** Type is not part of identity. `/cas/**` is served
  an explicit `Content-Type: application/octet-stream` so behaviour is defined
  rather than left to Firebase's extension table. Consequently
  `WebAssembly.instantiateStreaming()` will reject a `/cas/` URL — fetch to an
  `ArrayBuffer` and use `WebAssembly.instantiate`, or give the module a name.
- **The manifest lives outside `/cas/`.** `/cas/**` is served `immutable`; the
  manifest is the one mutable thing, so it sits at `/cas.json`.
- **Names are rewrites plus a per-name header rule — never redirects.** This is
  forced, and was measured rather than assumed: header rules match the _request_
  path, so a rule on the name can set `Content-Type` and `Content-Disposition`
  while `/cas/**` stays untyped. A 302 cannot, because the final response comes
  from `/cas/<hash>` and inherits its type. A rewrite _alone_ cannot either — the
  `.pdf` in the request path implies nothing. The header rule does the work.
  The cost is deduplication: an alias URL caches its own copy rather than
  converging on `/cas/<hash>`. Aliases are few and human-facing; anything
  referencing content by hash still converges.
- **`firebase.json` is hand-maintained, not generated** (it also holds the blog's
  301s). After any `add` that binds a name, update the rewrite _and_ its header
  rule, then run `pnpm cas -- check` — otherwise a rebound name silently
  serves the old object, or serves the right bytes untyped. `check` also rejects
  any redirect pointing into `/cas/`.

Note the hosting emulator does not implement range requests (returns 200 where
production returns 206). Production Firebase does support them, which is what
makes range-querying a stored SQLite database viable — but it can only be
confirmed against the deployed site.

### Deployment

Firebase Hosting serving from `build/` directory with 60-second cache headers.

**`cleanUrls: true` in `firebase.json` is load-bearing — do not remove it.** The
static adapter emits `blog.html` and `blog/<slug>.html`, but Firebase without
`cleanUrls` resolves only an exact path or `<path>/index.html`. Every
extensionless URL therefore missed and fell through to `404.html`, which — since
the adapter's `fallback` is an SPA shell — hydrated client-side and rendered the
right page anyway. The site looked fine in a browser while serving HTTP 404 and
an empty document to every crawler and link preview, and none of the prerendered
HTML was ever used. This was live for roughly a year before being caught.

Two consequences worth remembering:

- `pnpm preview` serves through Vite and ignores `firebase.json` entirely, so
  it cannot catch this class of bug. Verify hosting behaviour with
  `firebase emulators:start --only hosting` against a fresh `pnpm build`.
- Because the failure mode renders correctly in a browser, check the **status
  code**, not the page: `curl -sI https://tekne.dev/blog` must return `200`.

`firebase.json` also 301s the legacy bare slugs to their canonical series paths.
Redirects are evaluated _before_ static files, so those redirects win over the
identically-named prerendered pages that `buildPostLookup` also emits.

## Conventions

- Svelte 5 runes syntax (`$props()`, `{@render children()}`, etc.)
- Tabs for indentation, single quotes, no trailing commas (see .prettierrc)
- ESLint flat config (eslint.config.js)
