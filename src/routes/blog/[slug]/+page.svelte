<script>
	import * as config from '$lib/config';

	export let data;

    const { content, meta } = data;
</script>

<svelte:head>
	<meta name="author" content={meta.author || config.author}>
	{#if meta.title}
		<title>{meta.title}</title>
		<meta property="og:title" content={meta.title} />
	{/if}
	<meta property="og:type" content="article" />
</svelte:head>

<article>
	{#if meta.title}
		<h1>{meta.title}</h1>
		{#if meta.date}
			<p>Published: <time datetime={meta.date}>{meta.date}</time></p>
		{/if}
		<hr />
	{/if}
    <svelte:component this={content} />
</article>

<style>
	h1 {
		font-size: 2em;
		margin: 0px;
	}
</style>
