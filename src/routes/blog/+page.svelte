<script>
	import * as config from '$lib/config';

	export let data;
</script>

<svelte:head>
	<title>{config.title}</title>
</svelte:head>

<h1>Jad Ghalayini's Devlog</h1>

<ul>
	{#each data.posts as post}
		<li>
			<h2>
				<a href={post.path}>{post.meta.title}</a>
			</h2>
		</li>
		Published {post.meta.date}
	{/each}
</ul>

<style>
	ul {
		list-style-type: none;
        padding-left: 0;
	}
</style>
