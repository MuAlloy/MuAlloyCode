/*
    From section 2 of paper
    Colored, undirected trees
    Unbuggy version (including antireflexivity)
*/

abstract sig Color {}
one sig Red extends Color {}
one sig Blue extends Color {}

sig Node {
  neighbors: set Node,
  color: one Color 
} 	

fact undirected {
  neighbors = ~neighbors   -- symmetric
  
  -- no iden & neighbors      -- antireflexive
  // Fix: add "no iden & neighbors".
}

fact graphIsConnected {
  all n1: Node | all n2: Node-n1 | 
    n1 in n2.^neighbors }

fact treeAcyclic {
  all n1, n2: Node | n1 in n2.neighbors implies 
    n1 not in n2.^(neighbors-(n2->n1)) } 

run {} for 3 Node

val test9 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0
no neighbors
color = Node0->Red0
}}}}
}
@Test test9: run test9 for 3 expect 1

val test6 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1
neighbors = Node0->Node1 + Node1->Node0
color = Node0->Blue0 + Node1->Red0
}}}}
}
@Test test6: run test6 for 3 expect 1

val test15 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1
no neighbors
color = Node0->Blue0 + Node1->Red0
}}}}
}
@Test test15: run test15 for 3 expect 0

val test22 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1 + Node2
neighbors = Node0->Node1 + Node1->Node0 + Node1->Node2 + Node2->Node1
color = Node0->Blue0 + Node1->Blue0 + Node2->Red0
}}}}
}
@Test test22: run test22 for 3 expect 1

val test2 {
some disj Blue0: Blue {some disj Blue0: Color {some disj Node0, Node1: Node {
no Red
Blue = Blue0
Color = Blue0
Node = Node0 + Node1
neighbors = Node0->Node1 + Node1->Node0
color = Node0->Blue0 + Node1->Blue0
}}}
}
@Test test2: run test2 for 3 expect 0

val test4 {
some disj Red0: Red {some disj Red0: Color {some disj Node0, Node1: Node {
Red = Red0
no Blue
Color = Red0
Node = Node0 + Node1
neighbors = Node0->Node1 + Node1->Node0
color = Node0->Red0 + Node1->Red0
}}}
}
@Test test4: run test4 for 3 expect 0

val test17 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1 + Node2
neighbors = Node0->Node1 + Node0->Node2 + Node1->Node0 + Node2->Node0
color = Node0->Blue0 + Node1->Red0 + Node2->Red0
}}}}
}
@Test test17: run test17 for 3 expect 1

val test18 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1 + Node2
neighbors = Node0->Node1 + Node0->Node2 + Node1->Node0 + Node1->Node2 + Node2->Node0 + Node2->Node1
color = Node0->Blue0 + Node1->Red0 + Node2->Red0
}}}}
}
@Test test18: run test18 for 3 expect 0

val test5 {
some disj Red0: Red {some disj Blue0, Blue1: Blue {some disj Red0, Blue0, Blue1: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0 + Blue1
Color = Red0 + Blue0 + Blue1
Node = Node0 + Node1 + Node2
neighbors = Node0->Node2 + Node1->Node2 + Node2->Node0 + Node2->Node1
color = Node0->Blue1 + Node1->Blue0 + Node2->Blue0
}}}}
}
@Test test5: run test5 for 3 expect 0

val test14 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0
neighbors = Node0->Node0
color = Node0->Red0
}}}}
}
@Test test14: run test14 for 3 expect 0

val test20 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1 + Node2
neighbors = Node0->Node1 + Node0->Node2 + Node1->Node0 + Node1->Node2 + Node2->Node0 + Node2->Node1
color = Node0->Blue0 + Node1->Blue0 + Node2->Red0
}}}}
}
@Test test20: run test20 for 3 expect 0

val test3 {
some disj Red0, Red1: Red {some disj Blue0: Blue {some disj Blue0, Red0, Red1: Color {some disj Node0, Node1, Node2: Node {
Red = Red0 + Red1
Blue = Blue0
Color = Blue0 + Red0 + Red1
Node = Node0 + Node1 + Node2
neighbors = Node0->Node2 + Node1->Node2 + Node2->Node0 + Node2->Node1
color = Node0->Red1 + Node1->Red0 + Node2->Red0
}}}}
}
@Test test3: run test3 for 3 expect 0

val test7 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
no Node
no neighbors
no color
}}}
}
@Test test7: run test7 for 3 expect 1

val test21 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1 + Node2
neighbors = Node0->Node2 + Node1->Node2 + Node2->Node0 + Node2->Node1
color = Node0->Blue0 + Node1->Blue0 + Node2->Red0
}}}}
}
@Test test21: run test21 for 3 expect 1

val test16 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1
no neighbors
color = Node0->Red0 + Node1->Red0
}}}}
}
@Test test16: run test16 for 3 expect 0

val test19 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1 + Node2
neighbors = Node0->Node2 + Node1->Node2 + Node2->Node0 + Node2->Node1
color = Node0->Red0 + Node1->Red0 + Node2->Red0
}}}}
}
@Test test19: run test19 for 3 expect 1

val test11 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0
no neighbors
no color
}}}}
}
@Test test11: run test11 for 3 expect 0

val test8 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1 + Node2
neighbors = Node0->Node2 + Node1->Node2 + Node2->Node0 + Node2->Node1
color = Node0->Blue0 + Node1->Red0 + Node2->Blue0
}}}}
}
@Test test8: run test8 for 3 expect 1

val test13 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0, Node1, Node2: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0 + Node1 + Node2
neighbors = Node0->Node2 + Node1->Node0 + Node2->Node1
color = Node0->Blue0 + Node1->Red0 + Node2->Red0
}}}}
}
@Test test13: run test13 for 3 expect 0

val test10 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0
no neighbors
color = Node0->Red0 + Node0->Blue0
}}}}
}
@Test test10: run test10 for 3 expect 0

val test1 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0
no neighbors
color = Node0->Blue0
}}}}
}
@Test test1: run test1 for 3 expect 1

val test12 {
some disj Red0: Red {some disj Blue0: Blue {some disj Red0, Blue0: Color {some disj Node0: Node {
Red = Red0
Blue = Blue0
Color = Red0 + Blue0
Node = Node0
neighbors = Node0->Node0
color = Node0->Blue0
}}}}
}
@Test test12: run test12 for 3 expect 0