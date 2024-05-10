<script>
	import * as config from '$lib/config';

	export let data;
</script>

<svelte:head>
	<title>{config.title}</title>
</svelte:head>

<h1>Blog</h1>

<ul>
	{#each data.posts as post}
		<li>
			<h2>
				<a href={post.path}>{post.meta.title}</a>
			</h2>
		</li>
		Published {post.meta.published}
        {#if post.meta.edited}
            (Edited {post.meta.edited})
        {/if}
	{/each}
</ul>

<style>
	ul {
		list-style-type: none;
        padding-left: 0;
	}
</style>
