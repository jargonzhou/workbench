package graph.core;

/**
 * 广度优先搜索接口.
 */
public interface IBFS<GRAPH extends IGraph> {
  void bfs(GRAPH G, int s);
}
