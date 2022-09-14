
/*
  This assignment illustrates how specifications such as invariants and
  preconditions written in a formal language can help in removing
  errors in code.

  The assignment concerns a class "Person" that is used for Persons.

 */
 
class Person {



 /* isFemale is true iff the person is female */
 boolean isFemale;

 /* isMale is true iff the person is male */
 boolean isMale;
 //@ invariant isMale == true <==> isFemale == false;
 //@ invariant isMale == false <==> isFemale == true;

 Person father, mother; // These fields won't really be used  

 /* Age in years */
 int age;

 boolean isMarried;

 /* Reference to spouse if person is married, null otherwise */
 //@ nullable
 Person spouse;
 //@ invariant spouse != null ==> this == spouse.spouse ==> (spouse.isMale != this.isMale || spouse.isFemale != this.isFemale);
 /* welfare subsidy */
 int state_subsidy;
 /* save the DEFAULT_SUBSIDY */
 final int DEFAULT_SUBSIDY = 500;
 /* save increased subsidy */
 final int INCREASED_SUBSIDY = 600;
 //@ invariant (isMarried == true ==> state_subsidy == DEFAULT_SUBSIDY - (DEFAULT_SUBSIDY*30/100)) || (age > 65 && isMarried == true ==> state_subsidy == INCREASED_SUBSIDY - (INCREASED_SUBSIDY*30/100)) || (age <= 65 ==> state_subsidy == DEFAULT_SUBSIDY) || (age > 65 && isMarried == false ==> state_subsidy == INCREASED_SUBSIDY);
 /* CONSTRUCTOR */
 Person(boolean s, Person ma, Person pa) {
   age = 0;
   isMarried = false;
   this.isMale = s;
   this.isFemale = !s;
   mother = ma;
   father = pa;
   spouse = null;
   state_subsidy = DEFAULT_SUBSIDY;
 }

 /* METHODS */
 /* Marry to new_spouse */
 //@ requires spouse == null;
 //@ requires new_spouse != null ==> (new_spouse.isMale != this.isMale || new_spouse.isFemale != this.isFemale);
 void marry(Person new_spouse) {
  spouse = new_spouse;
  isMarried = true;
  if (age > 65){
  	state_subsidy = INCREASED_SUBSIDY - (INCREASED_SUBSIDY*30/100);
  }
  else{
  	state_subsidy = DEFAULT_SUBSIDY - (DEFAULT_SUBSIDY*30/100);
  }
 }

 /* Divorce from current spouse */
 //@ requires spouse != null;
 void divorce() {
  spouse = null;
  isMarried = false;
  if (age > 65){
  	state_subsidy = DEFAULT_SUBSIDY + 100;
  }
  else{
  	state_subsidy = DEFAULT_SUBSIDY;
  }
 }



 /* Person has a birthday and the age increases by one */
 //@ requires age < Integer.MAX_VALUE; 
 void haveBirthday() {
  age++;
  if (age > 65 && isMarried == false){
  	state_subsidy = DEFAULT_SUBSIDY + 100;
  }
  else if (age > 65 && isMarried == true){
  	state_subsidy = INCREASED_SUBSIDY - (INCREASED_SUBSIDY*30/100);
  }
 }
}
