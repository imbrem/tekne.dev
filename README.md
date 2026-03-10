# tekne.dev

Personal website and blog for [Jad Ghalayini](https://tekne.dev/), a PhD student at the University of Cambridge working on categorical semantics for SSA form.

Built with SvelteKit, deployed as a static site to Firebase Hosting.

## Tech Stack

- **Framework**: SvelteKit with static adapter
- **Markdown**: MDsveX (Svelte-flavored Markdown)
- **Code Highlighting**: Shiki (Nord theme)
- **Math**: KaTeX via remark-math + rehype-katex-svelte
- **Diagrams**: Mermaid
- **Styling**: CSS with Fira Code font
- **Deployment**: Firebase Hosting

## Development

```bash
npm install
npm run dev
```

## Building

```bash
npm run build
npm run preview  # preview the production build locally
```

## Deployment

```bash
npm run build
firebase deploy
```
