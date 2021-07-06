module unknown
open util/integer [] as integer
sig List {
header: (lone Node)
}
sig Node {
link: (lone Node)
}
pred Acyclic[l: List] {

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
