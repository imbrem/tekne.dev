<script lang="ts">
	import type { Picture } from 'vite-imagetools';

	let {
		src,
		alt,
		caption = '',
		// Article images span the content column, which is the 77rem `main` less
		// its 1rem padding. Without this the browser assumes 100vw and picks a
		// variant far larger than it will ever display. Keep in sync with the
		// `main` width in +layout.svelte.
		sizes = '(min-width: 77rem) 75rem, calc(100vw - 2rem)'
	}: {
		src: string | Picture;
		alt: string;
		caption?: string;
		sizes?: string;
	} = $props();
</script>

{#if caption}
	<figure>
		<enhanced:img {src} {alt} {sizes} loading="lazy" decoding="async" />
		<figcaption>{caption}</figcaption>
	</figure>
{:else}
	<enhanced:img {src} {alt} {sizes} loading="lazy" decoding="async" />
{/if}
