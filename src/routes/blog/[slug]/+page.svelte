<script>
	import * as config from '$lib/config';

	let { data } = $props();

	const Content = $derived(data.content);
	const meta = $derived(data.meta);
</script>

<svelte:head>
	<meta name="author" content={meta.author || config.author} />
	{#if meta.title}
		<title>{meta.title}</title>
		<meta property="og:title" content={meta.title} />
	{/if}
	<meta property="og:type" content="article" />
</svelte:head>

<article>
	{#if meta.title}
		<h1>{meta.title}</h1>
		{#if meta.published}
			<p>
				Published: <time datetime={meta.published}>{meta.published}</time>
				{#if meta.edited}(Edited: <time datetime={meta.edited}>{meta.edited}</time>){/if}
			</p>
		{/if}
		<hr />
	{/if}
	<Content />
</article>

<style>
	h1 {
		font-size: 2em;
		margin: 0px;
	}
</style>
