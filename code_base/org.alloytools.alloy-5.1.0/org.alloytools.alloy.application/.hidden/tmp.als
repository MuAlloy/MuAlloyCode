module unknown
open util/integer [] as integer
lone sig List {
header: (lone Node)
}
sig Node {
link: (lone Node)
}
pred Acyclic[l: List] {
(all n: (one ((l.header).(*link))) {
(n !in (n.(^link)))
})
}
pred NodesConnected[] {
(all n: (one Node) {
(some l: (one List) {
(n in ((l.header).(*link)))
})
})
}
pred run_1[] {

}



run run_1

pred Test1{
{
some disj list0 : List{
some disj node0 : Node {
List = list0
Node = node0
header = list0->node0
{Acyclic[list0]}
}}
}
}
run Test1 for 3

pred Test2{
{
some disj list0, list1, list2 : List{
some disj node0, node1, node2 : Node {
List = list0 + list1 + list2
Node = node0 + node1 + node2
header = list0->node0 + list1->node2
link = node0->node1 + node1->node1
{Acyclic[List - list0] and !Acyclic[list0]}
}}
}
}
run Test2 for 3

pred Test4{
{
some n : Node | n !in List.header.*link
{!NodesConnected[]}
}
}
run Test4 for 3

