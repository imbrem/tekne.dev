<script lang="ts">
	import '$lib/styles/style.css';
	import Header from '$lib/components/Header.svelte';
</script>

<Header />

<main>
	<slot />
</main>

<style>
	main {
		padding: 1rem;
		margin: 2rem auto;
		max-width: 77rem;
	}
</style>
