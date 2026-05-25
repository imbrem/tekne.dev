<script>
	import * as config from '$lib/config';

	let { data } = $props();

	const Content = $derived(data.content);
	const meta = $derived(data.meta);
	const canonicalPath = $derived(data.canonicalPath);
</script>

<svelte:head>
	<meta name="author" content={config.author} />
	{#if meta.title}
		<title>{meta.title}</title>
		<meta property="og:title" content={meta.title} />
	{/if}
	{#if meta.description}
		<meta name="description" content={meta.description} />
		<meta property="og:description" content={meta.description} />
	{/if}
	<meta property="og:type" content="article" />
	<link rel="canonical" href="{config.live_url}{canonicalPath.replace(/^\//, '')}" />
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
		{#if meta.series}
			<p class="series">Part of the <strong>{meta.series}</strong> series</p>
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

	.series {
		font-size: 0.9em;
		color: #aaa;
		font-style: italic;
		margin-top: 0;
	}
</style>
