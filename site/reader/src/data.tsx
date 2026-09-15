import { Fragment } from 'react';
import type { SiteData, SiteNode, Chapter } from './types';

// The data file sits next to index.html, so a relative URL works from any static server and
// from any base path. We fetch it once and keep derived indexes alongside it.
export async function loadSiteData(): Promise<SiteData> {
  const response = await fetch('./data/site.json', { cache: 'no-cache' });
  if (!response.ok) throw new Error(`Could not load data/site.json (${response.status}).`);
  return response.json() as Promise<SiteData>;
}

export type SiteIndex = {
  data: SiteData;
  nodeById: Map<string, SiteNode>;
  chapterBySlug: Map<string, Chapter>;
};

export function indexSiteData(data: SiteData): SiteIndex {
  const nodeById = new Map(data.nodes.map(node => [node.id, node]));
  const chapterBySlug = new Map(data.chapters.map(chapter => [chapter.slug, chapter]));
  return { data, nodeById, chapterBySlug };
}

export function shortName(name: string): string {
  return name.slice(name.lastIndexOf('.') + 1);
}

/** A dotted Lean name with break opportunities after each dot, so long names wrap sensibly. */
export function DottedName({ name }: { name: string }) {
  const parts = name.split('.');
  return <>{parts.map((part, index) => <Fragment key={index}>
    {index > 0 && <>.<wbr /></>}{part}
  </Fragment>)}</>;
}
