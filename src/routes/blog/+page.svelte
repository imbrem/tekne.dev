<script>
	import * as config from '$lib/config';

	let { data } = $props();
</script>

<svelte:head>
	<title>{config.title}</title>
</svelte:head>

<h1>Blog</h1>

<ul>
	{#each data.posts as post (post.path)}
		<li>
			<h2>
				<a href={post.path}>{post.meta.title}</a>
			</h2>
			Published {post.meta.published}
			{#if post.meta.edited}
				(Edited {post.meta.edited})
			{/if}
		</li>
	{/each}
</ul>

<style>
	ul {
		list-style-type: none;
		padding-left: 0;
	}
</style>
