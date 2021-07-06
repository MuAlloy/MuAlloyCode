sig Class {
  ext: lone Class
}

one sig Object extends Class {}

pred ObjectNoExt() {
  // Object does not extend any class.
  // Fix: replace "c.^ext" with "c.^~ext" or "c.~^ext".
  all c: Class | Object !in c.^ext
}

pred Acyclic() {
  // No class is a sub-class of itself (transitively).
  all c: Class | c !in c.^ext
}

pred AllExtObject() {
  // Each class other than Object is a sub-class of Object.
  // The body of the formula is wrong.
  // Fix: replace "c.*ext" with "Object.^~ext" or replace "c in c.*ext" with "Object in c.*ext".
  all c: Class - Object | c in c.*ext
}

pred ClassHierarchy() {
  ObjectNoExt
  Acyclic
  AllExtObject
}

run ClassHierarchy for 3

val test13 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
no ext
@cmd:{Acyclic[]}
}}
}
@Test test13: run test13 for 3 expect 1

val test14 {
some disj Object0: Object {some disj Object0: Class {
Object = Object0
Class = Object0
no ext
@cmd:{Acyclic[]}
}}
}
@Test test14: run test14 for 3 expect 1

val test18 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Object0 + Class0->Class0
@cmd:{AllExtObject[]}
}}
}
@Test test18: run test18 for 3 expect 0

val test7 {
some disj Object0, Object1: Object {some disj Class0, Object0, Object1: Class {
Object = Object0 + Object1
Class = Class0 + Object0 + Object1
ext = Class0->Object1 + Object0->Class0
}}
}
@Test test7: run test7 for 3 expect 0

val test11 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Object0 + Class0->Class0
@cmd:{Acyclic[]}
}}
}
@Test test11: run test11 for 3 expect 0

val test21 {
some disj Object0: Object {some disj Object0, Class0, Class1: Class {
Object = Object0
Class = Object0 + Class0 + Class1
ext = Class0->Class1 + Class1->Object0
@cmd:{AllExtObject[]}
}}
}
@Test test21: run test21 for 3 expect 1

val test15 {
some disj Object0: Object {some disj Object0, Class0, Class1: Class {
Object = Object0
Class = Object0 + Class0 + Class1
ext = Object0->Class1 + Class0->Class1 + Class1->Class0
@cmd:{Acyclic[]}
}}
}
@Test test15: run test15 for 3 expect 0

val test16 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Class0 + Class0->Class0
@cmd:{AllExtObject[]}
}}
}
@Test test16: run test16 for 3 expect 0

val test17 {
some disj Object0: Object {some disj Object0: Class {
Object = Object0
Class = Object0
no ext
@cmd:{AllExtObject[]}
}}
}
@Test test17: run test17 for 3 expect 1

val test24 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
no ext
@cmd:{ClassHierarchy[]}
}}
}
@Test test24: run test24 for 3 expect 0

val test8 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Class0 + Class0->Class0
@cmd:{ObjectNoExt[]}
}}
}
@Test test8: run test8 for 3 expect 0

val test5 {
some disj Class0, Class1, Class2: Class {
no Object
Class = Class0 + Class1 + Class2
ext = Class0->Class2 + Class1->Class0
}
}
@Test test5: run test5 for 3 expect 0

val test19 {
some disj Object0: Object {some disj Object0, Class0, Class1: Class {
Object = Object0
Class = Object0 + Class0 + Class1
ext = Class0->Object0 + Class1->Object0
@cmd:{AllExtObject[]}
}}
}
@Test test19: run test19 for 3 expect 1

val test3 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Class0->Class0
}}
}
@Test test3: run test3 for 3 expect 1

val test6 {
some disj Object0, Object1: Object {some disj Class0, Object0, Object1: Class {
Object = Object0 + Object1
Class = Class0 + Object0 + Object1
ext = Class0->Object1 + Object0->Object0 + Object1->Class0
}}
}
@Test test6: run test6 for 3 expect 0

val test9 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Class0->Class0
@cmd:{ObjectNoExt[]}
}}
}
@Test test9: run test9 for 3 expect 1

val test20 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Object0 + Class0->Object0
@cmd:{AllExtObject[]}
}}
}
@Test test20: run test20 for 3 expect 1

val test2 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Class0 + Class0->Object0 + Class0->Class0
}}
}
@Test test2: run test2 for 3 expect 0

val test22 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Class0 + Class0->Class0
@cmd:{ClassHierarchy[]}
}}
}
@Test test22: run test22 for 3 expect 0

val test12 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Class0 + Class0->Object0
@cmd:{Acyclic[]}
}}
}
@Test test12: run test12 for 3 expect 0

val test23 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Class0->Class0
@cmd:{ClassHierarchy[]}
}}
}
@Test test23: run test23 for 3 expect 0

val test10 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Class0 + Class0->Class0
@cmd:{Acyclic[]}
}}
}
@Test test10: run test10 for 3 expect 0

val test1 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Class0 + Class0->Class0
}}
}
@Test test1: run test1 for 3 expect 1

val test4 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Object0 + Object0->Class0 + Class0->Object0 + Class0->Class0
}}
}
@Test test4: run test4 for 3 expect 0

val test25 {
some disj Object0: Object {some disj Object0, Class0: Class {
Object = Object0
Class = Object0 + Class0
ext = Object0->Class0
@cmd:{ObjectNoExt[]}
}}
}
@Test test25: run test25 for 3 expect 0