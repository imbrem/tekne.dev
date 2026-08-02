/**
 * The KaTeX macros are defined once in katex-macros.json and mirrored into
 * .vscode/settings.json, because VS Code's markdown preview cannot import a
 * file. Mirrored definitions drift, and the failure is quiet: the preview
 * renders one thing and the built site another, with nothing to flag it.
 */

import { test, describe } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');

const macros = JSON.parse(readFileSync(join(ROOT, 'katex-macros.json'), 'utf8'));

// .vscode/settings.json is JSONC. Only whole-line comments are used here, and
// no macro value contains "//", so dropping those lines is sufficient.
const vscode = JSON.parse(
	readFileSync(join(ROOT, '.vscode', 'settings.json'), 'utf8')
		.split('\n')
		.filter((l) => !l.trim().startsWith('//'))
		.join('\n')
);

describe('katex macros', () => {
	test('the editor preview and the site share one definition', () => {
		assert.deepEqual(
			vscode['markdown.math.macros'],
			macros,
			'.vscode/settings.json has drifted from katex-macros.json'
		);
	});

	test('every macro is a control sequence expanding to something', () => {
		assert.ok(Object.keys(macros).length > 0);
		for (const [name, body] of Object.entries(macros)) {
			assert.match(name, /^\\[A-Za-z]+$/, `${name} should be \\ followed by letters`);
			assert.ok(body.length > 0, `${name} expands to nothing`);
		}
	});

	test('a macro taking an argument uses exactly #1', () => {
		// KaTeX infers arity from the highest #n, so a stray #2 would silently make
		// the macro require a second argument.
		for (const [name, body] of Object.entries(macros)) {
			const params = [...body.matchAll(/#(\d)/g)].map((m) => Number(m[1]));
			if (params.length === 0) continue;
			assert.deepEqual(
				[...new Set(params)].sort(),
				[1],
				`${name} should take exactly one argument, got #${[...new Set(params)].join(', #')}`
			);
		}
	});
});
