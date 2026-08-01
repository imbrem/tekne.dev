<script lang="ts">
	import * as config from '$lib/config';

	let { data } = $props();

	const absolute = (path: string) => `${config.live_url}${path.replace(/^\//, '')}`;
</script>

<!-- One <svelte:head> at the top level: it may contain blocks, but may not sit
     inside one. -->
<svelte:head>
	<meta name="author" content={config.author} />
	{#if data.kind === 'topic'}
		<title>{data.topic.title}</title>
		<meta name="description" content="Posts in {data.topic.title}" />
		<meta property="og:title" content={data.topic.title} />
		<link rel="canonical" href={absolute(data.topic.path)} />
	{:else}
		{#if data.meta.title}
			<title>{data.meta.title}</title>
			<meta property="og:title" content={data.meta.title} />
		{/if}
		{#if data.meta.description}
			<meta name="description" content={data.meta.description} />
			<meta property="og:description" content={data.meta.description} />
		{/if}
		<meta property="og:type" content="article" />
		<link rel="canonical" href={absolute(data.canonicalPath)} />
	{/if}
</svelte:head>

{#if data.kind === 'topic'}
	{@const topic = data.topic}
	<h1>{topic.title}</h1>
	<p class="count">
		{topic.posts.length}
		{topic.posts.length === 1 ? 'post' : 'posts'}, oldest first
	</p>
	<hr />

	<ul>
		{#each topic.posts as post, i (post.path)}
			<li>
				<h2>
					<span class="index">{i + 1}.</span>
					<a href={post.path}>{post.meta.title}</a>
				</h2>
				{#if post.meta.description}
					<p class="description">{post.meta.description}</p>
				{/if}
				<p class="dates">
					Published <time datetime={post.meta.published}>{post.meta.published}</time>
					{#if post.meta.edited}
						(Edited <time datetime={post.meta.edited}>{post.meta.edited}</time>)
					{/if}
				</p>
			</li>
		{/each}
	</ul>
{:else}
	{@const meta = data.meta}
	{@const Content = data.content}
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
				<p class="series">
					Part of the
					{#if data.topicPath}
						<a href={data.topicPath}><strong>{meta.series}</strong></a>
					{:else}
						<strong>{meta.series}</strong>
					{/if}
					series
				</p>
			{/if}
			<hr />
		{/if}
		<Content />
	</article>
{/if}

<style>
	h1 {
		font-size: 2em;
		margin: 0;
	}

	.series {
		font-size: 0.9em;
		color: #aaa;
		font-style: italic;
		margin-top: 0;
	}

	ul {
		list-style-type: none;
		padding-left: 0;
	}

	li h2 {
		margin-bottom: 0.25em;
	}

	.index {
		color: #aaa;
		margin-right: 0.25em;
	}

	.description,
	.dates {
		font-size: 0.9em;
		color: #aaa;
		margin: 0.25em 0;
	}

	.count {
		color: #aaa;
		font-size: 0.9em;
	}
</style>
