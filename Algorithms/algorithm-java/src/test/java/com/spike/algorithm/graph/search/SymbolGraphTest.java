package com.spike.algorithm.graph.search;

import com.google.common.base.Joiner;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.spike.algorithm.graph.core.SymbolGraph;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

public class SymbolGraphTest {
    @Test
    public void create() {
        // routes.txt
        List<String> lines = Lists.newArrayList("JFK MCO",
                "ORD DEN",
                "ORD HOU",
                "DFW PHX",
                "JFK ATL",
                "ORD DFW",
                "ORD PHX",
                "ATL HOU",
                "DEN PHX",
                "PHX LAX",
                "JFK ORD",
                "DEN LAS",
                "DFW HOU",
                "ORD ATL",
                "LAS LAX",
                "ATL MCO",
                "HOU MCO",
                "LAS PHX");
        Set<String> vertexes = Sets.newHashSet(lines);
        SymbolGraph SG = new SymbolGraph(Joiner.on(" ").join(vertexes).toString(), " ");
        for (String line : lines) {
            String[] edge = line.split(" ");
            SG.addEdge(edge[0], edge[1]);
        }

        System.out.print(SG.dump(false));
    }
}
