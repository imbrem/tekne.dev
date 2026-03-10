<script lang="ts">
	import '$lib/styles/style.css';
	import Header from '$lib/components/Header.svelte';
	import type { Snippet } from 'svelte';

	let { children }: { children: Snippet } = $props();
</script>

<Header />

<main>
	{@render children()}
</main>

<style>
	main {
		padding: 1rem;
		margin: 2rem auto;
		max-width: 77rem;
	}
</style>
