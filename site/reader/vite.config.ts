import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

// The site is served from a plain static directory, so every asset URL is relative
// to index.html (base './'). The generated data and the MathJax fonts live in public/
// and are copied into dist/ verbatim.
export default defineConfig({
  base: './',
  plugins: [react()],
  build: {
    emptyOutDir: true,
    outDir: 'dist',
  },
});
