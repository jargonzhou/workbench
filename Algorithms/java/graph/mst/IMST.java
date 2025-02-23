package graph.mst;

import graph.core.Edge;

/**
 * 最小生成树(Minimum Spanning Trees, MST)接口.
 * <p>
 * TODO(zhoujiagen) 实现PrimMST和KruskalMST.

 */
public interface IMST {

  /** 最小生成树中所有边. */
  Iterable<Edge> edges();

  /** 最小生成树的权重. */
  double weight();
}
