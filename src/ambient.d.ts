// Ambient declarations. This file must NOT contain a top-level import or
// export: that would make it a module, and `declare module` inside a module is
// an augmentation of an existing module rather than an ambient wildcard.

// @sveltejs/enhanced-img only declares `*?enhanced`, so an import carrying a
// width ladder does not typecheck on its own. A module pattern may contain
// exactly one wildcard, so the ladder is written *before* the flag —
// `?w=480;800&enhanced` rather than `?enhanced&w=480;800` — which lets this one
// declaration cover every ladder instead of needing a line per set of widths.
// Query order is irrelevant to the plugin, which only tests for the flag.
declare module '*&enhanced' {
	const value: import('vite-imagetools').Picture;
	export default value;
}
