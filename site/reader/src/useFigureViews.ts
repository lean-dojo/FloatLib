import { useLayoutEffect, type RefObject } from 'react';

type FigureView = { id: string; label: string; src: string; alt: string };

/** Keep the displayed plot and its download links on the same operation. */
export function useFigureViews(root: RefObject<HTMLDivElement | null>, html: string): void {
  useLayoutEffect(() => {
    const cleanups: (() => void)[] = [];
    const compact = window.matchMedia('(max-width: 600px)').matches;
    for (const figure of root.current?.querySelectorAll<HTMLElement>('.figure[data-views]') ?? []) {
      const views: FigureView[] = JSON.parse(figure.dataset.views!);
      const select = figure.querySelector<HTMLSelectElement>('select');
      const image = figure.querySelector<HTMLImageElement>('img');
      if (!select || !image) continue;
      const show = () => {
        const view = views.find(candidate => candidate.id === select.value);
        if (!view) return;
        image.src = view.src;
        image.alt = view.alt;
        figure.dataset.view = view.id;
        for (const link of figure.querySelectorAll<HTMLAnchorElement>('a[data-figure-file]')) {
          link.href = view.src;
        }
      };
      select.value = compact ? figure.dataset.compactDefault! : views[0].id;
      show();
      select.addEventListener('change', show);
      cleanups.push(() => select.removeEventListener('change', show));
    }
    return () => { for (const cleanup of cleanups) cleanup(); };
  }, [root, html]);
}
