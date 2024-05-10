<script>
	import * as config from '$lib/config';

	export let title;
	export let date;
	export let author;
</script>

<svelte:head>
	<meta name="author" content={author || config.author}>
	{#if title}
		<title>{title}</title>
		<meta property="og:title" content={title} />
	{/if}
	<meta property="og:type" content="article" />
</svelte:head>

<article>
	{#if title}
		<h1>{title}</h1>
		{#if date}
			<p>Published: <time datetime={date}>{date}</time></p>
		{/if}
		<hr />
	{/if}
	<slot />
</article>

<style>
	h1 {
		font-size: 2em;
		margin: 0px;
	}
</style>
