import { sveltekit } from '@sveltejs/kit/vite';
import { enhancedImages } from '@sveltejs/enhanced-img';
import { createLogger, defineConfig } from 'vite';

const logger = createLogger();
const originalWarn = logger.warn.bind(logger);
logger.warn = (msg, options) => {
	// Suppress cyclic cross-chunk reexport warning from Svelte internals (upstream issue)
	if (typeof msg === 'string' && msg.includes('circular dependency between chunks')) return;
	originalWarn(msg, options);
};

export default defineConfig({
	customLogger: logger,
	plugins: [enhancedImages(), sveltekit()],
	build: {
		chunkSizeWarningLimit: 1000
	}
});
