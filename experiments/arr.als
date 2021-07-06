sig Element {}

one sig Array {
  // Maps indexes to elements of Element.
  i2e: Int -> Element,
  // Represents the length of the array.
  length: Int
}

// Assume all objects are in the array.
fact Reachable {
  Element = Array.i2e[Int]
}

fact InBound {
  // All indexes should be greater than or equal to 0
  // and less than the array length
  all i:Array.i2e.Element | i >= 0
  all i:Array.i2e.Element | i < Array.length

  // Array length should be greater than equal to 0,
  // but also since there is a one-to-one mapping from
  // index to element, we restrict the array length to the
  // number of elements.
  // Fix: replace "Array.length = #Element" with "Array.length >= 0".
  Array.length = #Element
}

pred NoConflict() {
  // Each index maps to at most on element
  // Fix: replace "#Array.i2e[i] = 1" with "#Array.i2e[i] <= 1".
  all i:Array.i2e.Element | #Array.i2e[i] = 1
}

run NoConflict for 3

val test20 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->-8->Element0 + Array0->-7->Element0 + Array0->-6->Element0 + Array0->-5->Element0 + Array0->-4->Element0 + Array0->-3->Element0 + Array0->-2->Element0 + Array0->-1->Element0 + Array0->0->Element0 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0 + Array0->4->Element0 + Array0->5->Element0 + Array0->6->Element0 + Array0->7->Element0
length = Array0->1
}}
}
@Test test20: run test20 for 3 expect 0

val test36 {
some disj Array0: Array {
no Element
Array = Array0
no i2e
length = Array0->-1
}
}
@Test test36: run test36 for 3 expect 0

val test32 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->4->Element0
length = Array0->5
}}
}
@Test test32: run test32 for 3 expect 1

val test7 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element1 + Array0->1->Element0
length = Array0->-3 + Array0->0 + Array0->6
}}
}
@Test test7: run test7 for 3 expect 0

val test6 {
some disj Element0, Element1, Element2: Element {some disj Array0, Array1: Array {
Element = Element0 + Element1 + Element2
Array = Array0 + Array1
i2e = Array0->0->Element2 + Array0->1->Element1 + Array0->2->Element0 + Array0->2->Element2 + Array0->3->Element0 + Array0->3->Element2 + Array0->4->Element0 + Array0->4->Element2 + Array0->5->Element0 + Array0->5->Element2 + Array1->1->Element0 + Array1->1->Element1 + Array1->3->Element1
length = Array0->6 + Array1->0
}}
}
@Test test6: run test6 for 3 expect 0

val test29 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->0->Element0 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0 + Array0->4->Element0 + Array0->5->Element0
length = Array0->6
}}
}
@Test test29: run test29 for 3 expect 1

val test24 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->3->Element0
length = Array0->4
}}
}
@Test test24: run test24 for 3 expect 1

val test3 {
some disj Array0: Array {
no Element
Array = Array0
no i2e
length = Array0->0
}
}
@Test test3: run test3 for 3 expect 1

val test1 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element1 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0 + Array0->4->Element0 + Array0->5->Element0 + Array0->6->Element0
length = Array0->7
}}
}
@Test test1: run test1 for 3 expect 1

val test27 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element1 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0 + Array0->4->Element0 + Array0->5->Element1 + Array0->6->Element0
length = Array0->7
}}
}
@Test test27: run test27 for 3 expect 1

val test12 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->0->Element0 + Array0->1->Element0
length = Array0->3
@cmd:{NoConflict[]}
}}
}
@Test test12: run test12 for 3 expect 1

val test38 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element1 + Array0->1->Element0
length = Array0->2
@cmd:{NoConflict[]}
}}
}
@Test test38: run test38 for 3 expect 1

val test10 {
some disj Element0, Element1, Element2: Element {some disj Array0: Array {
Element = Element0 + Element1 + Element2
Array = Array0
i2e = Array0->0->Element0 + Array0->0->Element1 + Array0->0->Element2
length = Array0->5
@cmd:{NoConflict[]}
}}
}
@Test test10: run test10 for 3 expect 0

val test37 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->0->Element0
length = Array0->0
}}
}
@Test test37: run test37 for 3 expect 0

val test11 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->1->Element0
length = Array0->5
@cmd:{NoConflict[]}
}}
}
@Test test11: run test11 for 3 expect 1

val test33 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0 + Array0->6->Element0
length = Array0->0
}}
}
@Test test33: run test33 for 3 expect 0

val test22 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->-8->Element0 + Array0->-7->Element0 + Array0->-6->Element0 + Array0->-5->Element0 + Array0->-4->Element0 + Array0->-3->Element0 + Array0->-2->Element0 + Array0->-1->Element0
length = Array0->0
}}
}
@Test test22: run test22 for 3 expect 0

val test25 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element1 + Array0->1->Element0 + Array0->2->Element0
length = Array0->3
}}
}
@Test test25: run test25 for 3 expect 1

val test19 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->-8->Element0 + Array0->-7->Element0 + Array0->-6->Element0 + Array0->-5->Element0 + Array0->-4->Element0 + Array0->-3->Element0 + Array0->-2->Element0 + Array0->-1->Element0 + Array0->0->Element0 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0 + Array0->4->Element0 + Array0->5->Element0 + Array0->6->Element0 + Array0->7->Element0
length = Array0->0
}}
}
@Test test19: run test19 for 3 expect 0

val test13 {
some disj Array0: Array {
no Element
Array = Array0
no i2e
length = Array0->0
@cmd:{NoConflict[]}
}
}
@Test test13: run test13 for 3 expect 1

val test17 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->-8->Element0 + Array0->-7->Element0 + Array0->-6->Element0 + Array0->-5->Element0 + Array0->-4->Element0 + Array0->-3->Element0 + Array0->-2->Element0 + Array0->-1->Element0 + Array0->7->Element0
length = Array0->0
}}
}
@Test test17: run test17 for 3 expect 0

val test30 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->0->Element0 + Array0->1->Element0 + Array0->2->Element0 + Array0->4->Element0 + Array0->5->Element0
length = Array0->3
}}
}
@Test test30: run test30 for 3 expect 0

val test8 {
some disj Array0: Array {
no Element
Array = Array0
no i2e
no length
}
}
@Test test8: run test8 for 3 expect 0

val test14 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element0 + Array0->0->Element1
length = Array0->4
@cmd:{NoConflict[]}
}}
}
@Test test14: run test14 for 3 expect 0

val test18 {
some disj Array0: Array {
no Element
Array = Array0
no i2e
length = Array0->-6
}
}
@Test test18: run test18 for 3 expect 0

val test5 {
some disj Element0, Element1, Element2: Element {some disj Array0, Array1: Array {
Element = Element0 + Element1 + Element2
Array = Array0 + Array1
i2e = Array0->0->Element2 + Array0->1->Element1 + Array0->2->Element0 + Array0->2->Element2 + Array0->3->Element0 + Array0->3->Element2 + Array0->4->Element0 + Array0->4->Element2 + Array0->5->Element0 + Array0->5->Element2 + Array1->0->Element2 + Array1->1->Element0 + Array1->1->Element2 + Array1->5->Element1
length = Array0->6 + Array1->6
}}
}
@Test test5: run test5 for 3 expect 0

val test2 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element1 + Array0->2->Element0 + Array0->4->Element0 + Array0->6->Element0
length = Array0->7
}}
}
@Test test2: run test2 for 3 expect 1

val test23 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->0->Element0 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0
length = Array0->3
}}
}
@Test test23: run test23 for 3 expect 0

val test28 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->0->Element0 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0
length = Array0->4
}}
}
@Test test28: run test28 for 3 expect 1

val test35 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->0->Element0
length = Array0->3
}}
}
@Test test35: run test35 for 3 expect 1

val test9 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element0 + Array0->0->Element1
length = Array0->1 + Array0->3
}}
}
@Test test9: run test9 for 3 expect 0

val test26 {
some disj Element0, Element1: Element {some disj Array0: Array {
Element = Element0 + Element1
Array = Array0
i2e = Array0->0->Element1 + Array0->1->Element0 + Array0->2->Element1 + Array0->3->Element0 + Array0->4->Element0 + Array0->5->Element1 + Array0->6->Element0
length = Array0->7
}}
}
@Test test26: run test26 for 3 expect 1

val test21 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->-8->Element0 + Array0->-7->Element0 + Array0->-6->Element0 + Array0->-5->Element0 + Array0->-4->Element0 + Array0->-3->Element0 + Array0->-2->Element0 + Array0->-1->Element0 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0 + Array0->6->Element0 + Array0->7->Element0
length = Array0->0
}}
}
@Test test21: run test21 for 3 expect 0

val test31 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->0->Element0 + Array0->1->Element0 + Array0->5->Element0 + Array0->7->Element0
length = Array0->7
}}
}
@Test test31: run test31 for 3 expect 0

val test34 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->1->Element0
length = Array0->1
}}
}
@Test test34: run test34 for 3 expect 0

val test4 {

no Element
no Array
no i2e
no length

}
@Test test4: run test4 for 3 expect 0

val test15 {
some disj Element0: Element {some disj Array0: Array {
Element = Element0
Array = Array0
i2e = Array0->-8->Element0 + Array0->-7->Element0 + Array0->-6->Element0 + Array0->-5->Element0 + Array0->-4->Element0 + Array0->-3->Element0 + Array0->-2->Element0 + Array0->-1->Element0 + Array0->0->Element0 + Array0->1->Element0 + Array0->2->Element0 + Array0->3->Element0 + Array0->4->Element0 + Array0->5->Element0 + Array0->6->Element0 + Array0->7->Element0
length = Array0->-8
}}
}
@Test test15: run test15 for 3 expect 0

val test16 {
some disj Array0: Array {
no Element
Array = Array0
no i2e
length = Array0->-4
}
}
@Test test16: run test16 for 3 expect 0