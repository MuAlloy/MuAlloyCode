/*
Further simplification of Dan's work
access is granted to all assigned groups. 
problem: assigned groups defined as *at least* alas and peds.
fix: assigned groups definded as *only* alas and peds.
*/

//people
sig Person {
   member_of : some Group
}
pred CanEnter(p: Person, r:Room) {
	p.member_of in r.located_in
}

// groups 
sig Group {}
one sig alas extends Group {}  
one sig peds extends Group {}

//rooms
sig Room {
  located_in: set Group
}
one sig seclab extends Room {}
// the problem; this permits, but doesn't restrict
fact {
  // Fix: replace "alas in seclab.located_in and peds in seclab.located_in" with "alas + peds = seclab.located_in".
  alas in seclab.located_in and peds in seclab.located_in
}

// assertion
assert no_thief_in_seclab {
   all p : Person | CanEnter[p, seclab] implies alas in p.member_of or peds in p.member_of
}
check no_thief_in_seclab

/*
The specification
-----------------

We consider 3 classes:
- Persons
- Groups
- Rooms

There are two groups in particular: the systems and logic groups. 
There is one room in particular: the secure_lab.

We make the following assumptions:

1. Each person is a member_of some Group.

2. For each Room there is a set of Groups that are located_in it.

3. At least, the systems and logic groups are located_in the secure_lab.

4. A Person can_enter a Room only if the Person is a member_of a Group located_in the Room.

The assertion
--------------
 
Here is the assertion that we thought would be true:

* Each person that can_enter the secure_lab is a member_of the logic or the systems Group. 

--------------------------------------------------------------
*/

val test15 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0, seclab1: seclab {some disj seclab0, seclab1, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0 + seclab1
Room = seclab0 + seclab1 + Room0
located_in = seclab0->peds0 + seclab1->alas0 + Room0->peds0
}}}}}}
}
@Test test15: run test15 for 3 expect 0

val test9 {
some disj Person0, Person1: Person {some disj peds0: peds {some disj peds0, Group0: Group {some disj seclab0: seclab {some disj seclab0, Room0, Room1: Room {
Person = Person0 + Person1
member_of = Person0->peds0 + Person1->peds0 + Person1->Group0
no alas
peds = peds0
Group = peds0 + Group0
seclab = seclab0
Room = seclab0 + Room0 + Room1
located_in = seclab0->peds0 + Room1->peds0
}}}}}
}
@Test test9: run test9 for 3 expect 0

val test20 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0
Room = seclab0 + Room0
located_in = Room0->alas0 + Room0->peds0
}}}}}}
}
@Test test20: run test20 for 3 expect 0

val test17 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0, Group0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0 + Person0->Group0
alas = alas0
peds = peds0
Group = alas0 + peds0 + Group0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0 + Room0->peds0
@cmd:{CanEnter[Person0,Room0]}
}}}}}}
}
@Test test17: run test17 for 3 expect 0

val test14 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0
}}}}}}
}
@Test test14: run test14 for 3 expect 1

val test5 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0, Group0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0 + Person0->Group0
alas = alas0
peds = peds0
Group = alas0 + peds0 + Group0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0 + Room0->peds0
}}}}}}
}
@Test test5: run test5 for 3 expect 1

val test1 {
some disj Person0, Person1: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0 + Person1
member_of = Person0->peds0 + Person1->alas0
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0 + Room0->peds0
}}}}}}
}
@Test test1: run test1 for 3 expect 1

val test4 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0: seclab {some disj seclab0: Room {
Person = Person0
no member_of
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0
Room = seclab0
located_in = seclab0->alas0 + seclab0->peds0
}}}}}}
}
@Test test4: run test4 for 3 expect 0

val test2 {
some disj Person0, Person1: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0 + Person1
member_of = Person0->peds0 + Person1->alas0
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0
}}}}}}
}
@Test test2: run test2 for 3 expect 1

val test18 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0, Group0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0 + Group0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0 + Room0->peds0 + Room0->Group0
@cmd:{CanEnter[Person0,Room0]}
}}}}}}
}
@Test test18: run test18 for 3 expect 1

val test8 {
some disj Person0, Person1: Person {some disj alas0, alas1: alas {some disj peds0: peds {some disj peds0, alas0, alas1: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0 + Person1
member_of = Person0->alas0 + Person1->peds0 + Person1->alas1
alas = alas0 + alas1
peds = peds0
Group = peds0 + alas0 + alas1
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->peds0 + seclab0->alas0 + seclab0->alas1 + Room0->peds0 + Room0->alas0
}}}}}}
}
@Test test8: run test8 for 3 expect 0

val test6 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0 + Room0->peds0
}}}}}}
}
@Test test6: run test6 for 3 expect 1

val test12 {
some disj Person0, Person1: Person {some disj alas0: alas {some disj alas0, Group0: Group {some disj seclab0: seclab {some disj seclab0, Room0, Room1: Room {
Person = Person0 + Person1
member_of = Person0->alas0 + Person1->alas0 + Person1->Group0
alas = alas0
no peds
Group = alas0 + Group0
seclab = seclab0
Room = seclab0 + Room0 + Room1
located_in = seclab0->alas0 + Room1->alas0
}}}}}
}
@Test test12: run test12 for 3 expect 0

val test3 {
some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
no Person
no member_of
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0 + Room0->peds0
}}}}}
}
@Test test3: run test3 for 3 expect 1

val test19 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0 + Room0->peds0
@cmd:{CanEnter[Person0,Room0]}
}}}}}}
}
@Test test19: run test19 for 3 expect 1

val test7 {
some disj Person0, Person1: Person {some disj peds0: peds {some disj peds0, Group0: Group {some disj seclab0: seclab {some disj seclab0: Room {
Person = Person0 + Person1
member_of = Person0->peds0 + Person1->peds0 + Person1->Group0
no alas
peds = peds0
Group = peds0 + Group0
seclab = seclab0
Room = seclab0
located_in = seclab0->peds0
}}}}}
}
@Test test7: run test7 for 3 expect 0

val test13 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0, Group0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0 + Group0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + Room0->alas0 + Room0->peds0 + Room0->Group0
}}}}}}
}
@Test test13: run test13 for 3 expect 1

val test16 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0: Group {some disj seclab0, seclab1: seclab {some disj seclab0, seclab1, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0
seclab = seclab0 + seclab1
Room = seclab0 + seclab1 + Room0
located_in = seclab1->alas0 + seclab1->peds0
}}}}}}
}
@Test test16: run test16 for 3 expect 0

val test11 {
some disj Person0, Person1: Person {some disj alas0: alas {some disj peds0, peds1: peds {some disj alas0, peds0, peds1: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0 + Person1
member_of = Person0->peds0 + Person1->alas0 + Person1->peds1
alas = alas0
peds = peds0 + peds1
Group = alas0 + peds0 + peds1
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + seclab0->peds1 + Room0->alas0 + Room0->peds0
}}}}}}
}
@Test test11: run test11 for 3 expect 0

val test21 {
some disj Person0: Person {some disj alas0: alas {some disj peds0: peds {some disj alas0, peds0, Group0: Group {some disj seclab0: seclab {some disj seclab0, Room0: Room {
Person = Person0
member_of = Person0->alas0 + Person0->peds0
alas = alas0
peds = peds0
Group = alas0 + peds0 + Group0
seclab = seclab0
Room = seclab0 + Room0
located_in = seclab0->alas0 + seclab0->peds0 + seclab0->Group0 + Room0->alas0 + Room0->peds0
}}}}}}
}
@Test test21: run test21 for 3 expect 0

val test10 {
some disj Person0, Person1: Person {some disj alas0: alas {some disj alas0, Group0: Group {some disj seclab0: seclab {some disj seclab0: Room {
Person = Person0 + Person1
member_of = Person0->alas0 + Person1->alas0 + Person1->Group0
alas = alas0
no peds
Group = alas0 + Group0
seclab = seclab0
Room = seclab0
located_in = seclab0->alas0
}}}}}
}
@Test test10: run test10 for 3 expect 0