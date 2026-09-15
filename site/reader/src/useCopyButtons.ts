import { useEffect, type RefObject } from 'react';

/** Activate the Copy buttons in Markdown rendered by the data builder. */
export function useCopyButtons(root: RefObject<HTMLDivElement | null>, html: string): void {
  useEffect(() => {
    const element = root.current;
    if (!element) return;
    const timers = new Map<HTMLButtonElement, number>();
    const copy = async (event: MouseEvent) => {
      const target = event.target;
      if (!(target instanceof Element)) return;
      const button = target.closest<HTMLButtonElement>('button[data-copy-code]');
      if (!button || !element.contains(button)) return;
      window.clearTimeout(timers.get(button));
      let label: string;
      try {
        await navigator.clipboard.writeText(button.dataset.copyCode ?? '');
        label = 'Copied';
      } catch {
        label = 'Copy failed';
      }
      if (!button.isConnected) return;
      button.textContent = label;
      timers.set(button, window.setTimeout(() => {
        button.textContent = 'Copy';
        timers.delete(button);
      }, 1800));
    };
    element.addEventListener('click', copy);
    return () => {
      element.removeEventListener('click', copy);
      for (const timer of timers.values()) window.clearTimeout(timer);
    };
  }, [root, html]);
}
