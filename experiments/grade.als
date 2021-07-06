/*   Dan Dougherty, 12/16

Alloy gradebook spec, with some names changed:
Each relation is now denoted by (i) using an appropriate legal English verb-phrase, then
(ii)  eliding "is" is for concision. 
This facilitates matching English translation to spec.

Also: rephrased assertion as an implication.
*/

abstract sig Person {}
sig Student extends Person {}
sig Professor extends Person {}
sig Class {
	assistant_for: set Student,   // as in : "is TA for"
	instructor_of: one Professor
}
sig Assignment {
	associated_with: one Class,
	assigned_to: some Student
}

pred PolicyAllowsGrading(s: Person, a: Assignment) {
	s in a.associated_with.assistant_for or s in a.associated_with.instructor_of
	// Fix: add "s !in a.assigned_to".
}
assert NoOneCanGradeTheirOwnAssignment {
	all s : Person | all a: Assignment | PolicyAllowsGrading[s, a] implies not s in a.assigned_to 
}

check NoOneCanGradeTheirOwnAssignment

/*

The specification
-----------------

We consider 3 classes:

- Persons
- Classes
- Assignments

The class of Persons is partitioned into 2 non-overlapping subclasses:

- Students
- Professors

We make the following assumptions:

1. For each Class there is a single Professor who is the instructor_of it.

2. For each Class there is a set of Students who are the assistants_for it.

3. For each Assignment there is a single Class associated_with it

4. For each Assignment there is a set of Students assigned_to it.

5. A Person can_grade an Assignment only if either the
    person is an assistant_for the  Class associated_with the Assignment
    or the Person is the Professor who is the instructor_of that
    Class.

The assertion
--------------
 
Here is the assertion that we thought would be true:

* There cannot exist a Person who is allowed to grade an Assignment
  asigned_to them.


--------------------------------------------------------------

Notes/Qs
----------

Why was the PolicyAllowsGrading specified as a pred rather than a
fact?   If a fact then NoOneCanGradeTheirOwnAssignment 
is easier to state.   

*/

val test36 {
some disj Student0: Student {some disj Professor0, Professor1: Professor {some disj Student0, Professor0, Professor1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0 + Professor1
Person = Student0 + Professor0 + Professor1
Class = Class0 + Class1 + Class2
assistant_for = Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor1
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class0
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Professor1,Assignment2]}
}}}}}
}
@Test test36: run test36 for 3 expect 0

val test5 {
some disj Professor0, Professor1, Professor2: Professor {some disj Professor0, Professor1, Professor2: Person {some disj Class0, Class1, Class2: Class {
no Student
Professor = Professor0 + Professor1 + Professor2
Person = Professor0 + Professor1 + Professor2
Class = Class0 + Class1 + Class2
no assistant_for
instructor_of = Class0->Professor2 + Class1->Professor1 + Class2->Professor0
no Assignment
no associated_with
no assigned_to
}}}
}
@Test test5: run test5 for 3 expect 1

val test26 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class0->Student1 + Class1->Student0 + Class1->Student1 + Class2->Student0 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student1 + Assignment1->Student0 + Assignment1->Student1 + Assignment2->Student1
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test26: run test26 for 3 expect 0

val test39 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class0->Student1 + Class1->Student0 + Class1->Student1 + Class2->Student0 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student1 + Assignment1->Student1 + Assignment2->Student0 + Assignment2->Student1
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test39: run test39 for 3 expect 0

val test2 {

no Student
no Professor
no Person
no Class
no assistant_for
no instructor_of
no Assignment
no associated_with
no assigned_to

}
@Test test2: run test2 for 3 expect 1

val test3 {
some disj Student0, Student1: Student {some disj Student0, Student1: Person {
Student = Student0 + Student1
no Professor
Person = Student0 + Student1
no Class
no assistant_for
no instructor_of
no Assignment
no associated_with
no assigned_to
}}
}
@Test test3: run test3 for 3 expect 1

val test14 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class2->Student0
instructor_of = Class0->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
}}}}}
}
@Test test14: run test14 for 3 expect 0

val test41 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class0->Student1 + Class1->Student1 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0 + Assignment2->Student1
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test41: run test41 for 3 expect 0

val test21 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class0 + Assignment2->Class2
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
}}}}}
}
@Test test21: run test21 for 3 expect 0

val test25 {
some disj Student0: Student {some disj Professor0: Professor {some disj Professor0, Student0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Professor0 + Student0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class2
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Student0,Assignment2]}
}}}}}
}
@Test test25: run test25 for 3 expect 0

val test7 {
some disj Student0: Student {some disj Student0: Person {
Student = Student0
no Professor
Person = Student0
no Class
no assistant_for
no instructor_of
no Assignment
no associated_with
no assigned_to
}}
}
@Test test7: run test7 for 3 expect 1

val test24 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Student1, Professor0: Person {some disj Class0: Class {some disj Assignment0, Assignment1: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Student1 + Professor0
Class = Class0
assistant_for = Class0->Student1
instructor_of = Class0->Professor0
Assignment = Assignment0 + Assignment1
associated_with = Assignment0->Class0 + Assignment1->Class0
assigned_to = Assignment0->Student0 + Assignment0->Student1 + Assignment1->Student0 + Assignment1->Student1
}}}}}
}
@Test test24: run test24 for 3 expect 1

val test1 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
}}}}}
}
@Test test1: run test1 for 3 expect 1

val test38 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Student1, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Student1 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student1 + Class1->Student0 + Class1->Student1 + Class2->Student0 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class0
assigned_to = Assignment0->Student1 + Assignment1->Student0 + Assignment2->Student1
@cmd:{PolicyAllowsGrading[Professor0,Assignment2]}
}}}}}
}
@Test test38: run test38 for 3 expect 1

val test16 {
some disj Professor0, Professor1: Professor {some disj Professor0, Professor1: Person {some disj Class0, Class1, Class2: Class {
no Student
Professor = Professor0 + Professor1
Person = Professor0 + Professor1
Class = Class0 + Class1 + Class2
no assistant_for
instructor_of = Class0->Professor1 + Class1->Professor1 + Class2->Professor0 + Class2->Professor1
no Assignment
no associated_with
no assigned_to
}}}
}
@Test test16: run test16 for 3 expect 0

val test20 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment1->Class2 + Assignment2->Class2
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
}}}}}
}
@Test test20: run test20 for 3 expect 0

val test18 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
no Assignment
no associated_with
no assigned_to
}}}}
}
@Test test18: run test18 for 3 expect 1

val test31 {
some disj Student0: Student {some disj Professor0, Professor1: Professor {some disj Student0, Professor0, Professor1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0: Assignment {
Student = Student0
Professor = Professor0 + Professor1
Person = Student0 + Professor0 + Professor1
Class = Class0 + Class1 + Class2
assistant_for = Class1->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor1
Assignment = Assignment0
associated_with = Assignment0->Class2
assigned_to = Assignment0->Student0
@cmd:{PolicyAllowsGrading[Professor1,Assignment0]}
}}}}}
}
@Test test31: run test31 for 3 expect 1

val test35 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student1 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment1->Student1 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test35: run test35 for 3 expect 0

val test9 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1
associated_with = Assignment0->Class2 + Assignment1->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0
}}}}}
}
@Test test9: run test9 for 3 expect 1

val test40 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0
associated_with = Assignment0->Class2
assigned_to = Assignment0->Student0
@cmd:{PolicyAllowsGrading[Professor0,Assignment0]}
}}}}}
}
@Test test40: run test40 for 3 expect 1

val test22 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0
assistant_for = Class0->Student0
instructor_of = Class0->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class0 + Assignment1->Class0 + Assignment2->Class0
no assigned_to
}}}}}
}
@Test test22: run test22 for 3 expect 0

val test10 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
no Class
no assistant_for
no instructor_of
no Assignment
no associated_with
no assigned_to
}}}
}
@Test test10: run test10 for 3 expect 1

val test6 {
some disj Student0: Student {some disj Professor0, Professor1: Professor {some disj Student0, Professor0, Professor1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1: Assignment {
Student = Student0
Professor = Professor0 + Professor1
Person = Student0 + Professor0 + Professor1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor1 + Class1->Professor0 + Class2->Professor1
Assignment = Assignment0 + Assignment1
associated_with = Assignment0->Class2 + Assignment1->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0
}}}}}
}
@Test test6: run test6 for 3 expect 1

val test13 {
some disj Student0: Student {some disj Professor0, Professor1: Professor {some disj Student0, Professor0, Professor1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1: Assignment {
Student = Student0
Professor = Professor0 + Professor1
Person = Student0 + Professor0 + Professor1
Class = Class0 + Class1 + Class2
assistant_for = Class1->Student0
instructor_of = Class0->Professor1 + Class1->Professor1 + Class2->Professor1
Assignment = Assignment0 + Assignment1
associated_with = Assignment0->Class2 + Assignment1->Class2
assigned_to = Assignment0->Student0 + Assignment1->Student0
}}}}}
}
@Test test13: run test13 for 3 expect 1

val test19 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class0 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
}}}}}
}
@Test test19: run test19 for 3 expect 0

val test37 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student1 + Class1->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class2
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment1->Student1 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test37: run test37 for 3 expect 0

val test4 {
some disj Professor0: Professor {some disj Professor0: Person {some disj Class0: Class {
no Student
Professor = Professor0
Person = Professor0
Class = Class0
no assistant_for
instructor_of = Class0->Professor0
no Assignment
no associated_with
no assigned_to
}}}
}
@Test test4: run test4 for 3 expect 1

val test33 {
some disj Student0: Student {some disj Professor0, Professor1: Professor {some disj Student0, Professor0, Professor1: Person {some disj Class0, Class1: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0 + Professor1
Person = Student0 + Professor0 + Professor1
Class = Class0 + Class1
no assistant_for
instructor_of = Class0->Professor1 + Class1->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class1 + Assignment1->Class0 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Professor1,Assignment2]}
}}}}}
}
@Test test33: run test33 for 3 expect 0

val test17 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Student1, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Student1 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student1 + Class1->Student0 + Class1->Student1 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student1 + Assignment1->Student1 + Assignment2->Student0
}}}}}
}
@Test test17: run test17 for 3 expect 1

val test27 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student1 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class0
assigned_to = Assignment0->Student1 + Assignment1->Student1 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test27: run test27 for 3 expect 0

val test15 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class2 + Assignment2->Class2
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
}}}}}
}
@Test test15: run test15 for 3 expect 0

val test12 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
}}}}}
}
@Test test12: run test12 for 3 expect 1

val test29 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Professor0,Assignment2]}
}}}}}
}
@Test test29: run test29 for 3 expect 1

val test11 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Student1, Professor0: Person {some disj Class0, Class1, Class2: Class {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Student1 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student1 + Class1->Student0 + Class1->Student1 + Class2->Student0 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
no Assignment
no associated_with
no assigned_to
}}}}
}
@Test test11: run test11 for 3 expect 1

val test23 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class2 + Assignment2->Class2
no assigned_to
}}}}}
}
@Test test23: run test23 for 3 expect 0

val test28 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class0->Student1 + Class2->Student0 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class2
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0 + Assignment2->Student1
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test28: run test28 for 3 expect 0

val test32 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class0->Student1 + Class2->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class0
assigned_to = Assignment0->Student1 + Assignment1->Student0 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test32: run test32 for 3 expect 1

val test8 {
some disj Student0: Student {some disj Professor0: Professor {some disj Student0, Professor0: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0
Professor = Professor0
Person = Student0 + Professor0
Class = Class0 + Class1 + Class2
assistant_for = Class0->Student0 + Class1->Student0 + Class2->Student0
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class2 + Assignment2->Class1
assigned_to = Assignment0->Student0 + Assignment1->Student0 + Assignment2->Student0
}}}}}
}
@Test test8: run test8 for 3 expect 1

val test30 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1
assistant_for = Class0->Student1 + Class1->Student1
instructor_of = Class0->Professor0 + Class1->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class1 + Assignment1->Class0 + Assignment2->Class0
assigned_to = Assignment0->Student1 + Assignment1->Student1 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test30: run test30 for 3 expect 1

val test34 {
some disj Student0, Student1: Student {some disj Professor0: Professor {some disj Student0, Professor0, Student1: Person {some disj Class0, Class1, Class2: Class {some disj Assignment0, Assignment1, Assignment2: Assignment {
Student = Student0 + Student1
Professor = Professor0
Person = Student0 + Professor0 + Student1
Class = Class0 + Class1 + Class2
assistant_for = Class1->Student1
instructor_of = Class0->Professor0 + Class1->Professor0 + Class2->Professor0
Assignment = Assignment0 + Assignment1 + Assignment2
associated_with = Assignment0->Class2 + Assignment1->Class1 + Assignment2->Class1
assigned_to = Assignment0->Student1 + Assignment1->Student1 + Assignment2->Student0
@cmd:{PolicyAllowsGrading[Student1,Assignment2]}
}}}}}
}
@Test test34: run test34 for 3 expect 1