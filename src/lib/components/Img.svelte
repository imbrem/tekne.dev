<script lang="ts">
	import type { Picture } from 'vite-imagetools';

	let {
		src,
		alt,
		caption = ''
	}: {
		src: string | Picture;
		alt: string;
		caption?: string;
	} = $props();
</script>

{#if caption}
	<figure>
		<enhanced:img {src} {alt} loading="lazy" decoding="async" />
		<figcaption>{caption}</figcaption>
	</figure>
{:else}
	<enhanced:img {src} {alt} loading="lazy" decoding="async" />
{/if}
