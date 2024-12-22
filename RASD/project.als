enum ApplicationStatus {Submitted, UnderReview, Accepted, Rejected}
enum InternshipStatus {Open, Ongoing, Closed}
enum InterviewStatus{Scheduled, Hired, Refused}

enum Bool{True, False}

abstract sig CV {}
abstract sig User {}

sig Student extends User {
	//We assume that the student has already uploaded his CV
	cv: one CV,
	var isHired: one Bool
}

sig Company extends User {
	var internships: set Internship
}

sig Internship {
    var iState: one InternshipStatus,
} {one c: Company | this in c.internships}

sig Notification {
	between: Student -> Internship,
	notifiedCompany: one Company
} {
	getInternshipNotification[this] in notifiedCompany.internships
}

sig Application {
    var aState: one ApplicationStatus,
	var apply: Student -> Internship
} {
	((getStudent[this] = none and getInternship[this] = none) or 
	(some s: Student, i: Internship | getStudent[this] = s and getInternship[this] = i)) and
	((getStudent[this] = none and getInternship[this] = none) iff aState = none)
}

sig Interview {
	var application: lone Application,
	var state: lone InterviewStatus
} {
	(lone a: Application | (a.aState = Accepted and a in application)) and
	(state = none iff application = none)
}

/**********FUNCTIONS**********/

// returns the student that wrote the application
fun getStudent[a: Application]: one Student {
	(a.apply).Internship
}

// Returns the internship the application applied to -> RISCRIVI
fun getInternship[a: Application]: one Internship {
	Student.(a.apply)
}

//Returns the student that is notified about an internship
fun getNotifiedStudent[n: Notification]: one Student {
	(n.between).Internship
}

//Returns the internship the student is notified about
fun getInternshipNotification [n: Notification]: one Internship {
	Student.(n.between)
}

//Returns the company who advertise the internship
fun getCompany[i: Internship]: one Company {
	{c: Company | i in c.internships}
}

/**********FACTS**********/

//Two students cannot have the same CV
fact {
	all disj s1, s2: Student | not (s1.cv = s2.cv) or (s1.cv = s2.cv and s1.cv = none) 
}

//Every application belong to one and only one student
fact{
	all a: Application |
		let s = getStudent[a] | #s <= 1
}

//Every application is sent for one and only one internship
fact {
	all a: Application |
		let i = getInternship[a] | #i <= 1
}

//Every notification is sent to one and only one existing student
fact {
	all n: Notification |
		let s = getNotifiedStudent[n] | #s = 1
}

//Every application is about one and only one existing internship
fact {
	all n: Notification |
		let i = getInternshipNotification[n] | #i = 1
}

//Application never changes -> RISCRIVI
fact {
	all i: Interview | not(i.application = none) implies always (i.application' = i.application)
}

//The application discussed during the interview is unique
fact {
	always(all a: Application | lone i: Interview | i.application = a)
}

//Lifecycle of Internship
//... Open -> Ongoing -> Closed
/*
fact {
    all i: Internship |
        always (i.iState = Open implies 
            (eventually i.iState = Ongoing and historically i.iState = Open)) 
        and always (i.iState = Ongoing implies 
            (eventually i.iState = Closed and historically i.iState = Ongoing)) 
        and always (i.iState = Closed implies 
            (historically i.iState = Ongoing and after always (i.iState = Closed)))
}
*/
/*
fact {
	  all i: Internship |
        always (i.iState = Open implies 
            ((eventually i.iState = Ongoing) and (historically i.iState = Open))) 
}
*/
fact {
	all i: Internship |
		always (i.iState = Ongoing implies 
            ((eventually i.iState = Closed) and (historically i.iState = Open))) 
}

/*
fact {

    all i: Internship |
        always (i.iState = Open implies 
            (eventually i.iState = Ongoing and historically i.iState = Open)) 
        and always (i.iState = Ongoing implies 
            (eventually i.iState = Closed and historically i.iState = Ongoing)) 
        and always (i.iState = Closed implies 
            (historically i.iState = Ongoing))
}
*/
fact {
	all i: Internship | always (i.iState = Closed implies after always (i.iState = Closed))
}
//Lifecycle of Application
//... Submitted -> UnderReview -> Accepted or Rejected
fact{
	all a: Application | 
		always (a.aState = Submitted implies
				(historically a.aState = Submitted) and
				(eventually a.aState = UnderReview))
}

fact {
	all a: Application |
		always (a.aState = UnderReview implies
			(eventually (a.aState = Accepted or a.aState = Rejected)))
}

fact{
	all a: Application | 
		always (a.aState = Accepted implies
				(after always a.aState = Accepted))
}

fact{
	all a: Application | 
		always (a.aState = Rejected implies
				(after always a.aState = Rejected))
}

//Lifecycle of Interview
// ... -> Scheduled -> Hired or Refused
fact {
	all i: Interview |
		always (i.state = Scheduled implies
			eventually (i.state = Hired or i.state = Refused))
}

fact {
	all i: Interview |
		always (i.state = Refused implies
				once i.state = Scheduled and
				after always i.state = Refused)
}

fact {
	all i: Interview |
		always (i.state = Hired implies
				once i.state = Scheduled and
				after always i.state = Hired)
}

//Student Lifecycle
fact {
	all s: Student |
		always (s.isHired = True implies
			after always(s.isHired = True))
}

//Student cannot be hired if he has not been interviewed
fact {
	all s: Student |
		s.isHired = False releases (no i: Interview | getStudent[i.application] = s and i.state = Hired)
}

//Student can apply only to open or ongoing internships -> Checked
fact {
	all a: Application |
		always (a.aState = Submitted
			implies getInternship[a].iState = Open or getInternship[a].iState = Ongoing)
}

//Student cannot apply twice to the same internship
fact{
	always(
		no disj a1, a2: Application | getStudent[a1] = getStudent[a2] and 
			getInternship[a1] = getInternship[a2]
	) 
}

//Student is hired if and only if interview is in Hired state and isHired is true -> RISCRIVI MEGLIO -> Checked
fact {
	all s: Student | s.isHired = True implies
		(some i: Interview | getStudent[i.application] = s and i.state = Hired)
}

//If student is hired he cannot receive any notification
fact {
	all s: Student | s.isHired = True implies 
		(no n: Notification | getNotifiedStudent[n] = s)
}

//Companies can be notified iff they have at least one opened internship announce
fact {
	all c: Company | (c.internships = none or 
			(no i: Internship | i in c.internships and (i.iState = Open or i.iState = Ongoing))) implies
		(no n: Notification | n.notifiedCompany = c)
}

//Student cannot be notified twice about the same internship
fact {
	no disj n1, n2: Notification | always(getNotifiedStudent[n1] = getNotifiedStudent[n2] and
		getInternshipNotification[n1] = getInternshipNotification[n2])
}

//If an internship is closed there are no application submitted for it
fact {
    all i: Internship |
        i.iState = Closed implies no a: Application | 
			getInternship[a] = i and (a.aState in Submitted or a.aState in UnderReview) 
}

//If application is not accepted there are no interviews scheduled for it
fact {
	all a: Application |
		(not (a.aState = Accepted) implies
			(no i: Interview | i.application = a))
}

//Interview can be scheduled only if the application was accepted
fact {
	all i: Interview, a: Application | (i.state = Scheduled and i.application = a) iff 
											a.aState = Accepted
}

/*
PROBLEMI:
	1) Interview hired e student non hired -> succede perchè eventually student può tornare non hired
	2) Non esistono interview
	3) Esistono interview per application in UnderReview o Submitted
	4) Student passa ad Hired anche senza interview
*/

/**********PREDICATES**********/

//Student applies to an internship but he is refused
pred studentApplies1 [s: Student, i: Internship] {
	#Student = 1
	#Internship = 1
	historically(i.iState = Open) and
		(
			s.isHired = False and
			after (one a1: Application | 
				getStudent[a1] = s and getInternship[a1] = i and a1.aState = Submitted and
			after(a1.aState = UnderReview and
			after(a1.aState = Rejected and 
					(no iv1: Interview | iv1.application = a1) and s.isHired = False)))
		)
}

//Student applies to an internship, his application is accepted, but he is refused during the interview
pred studentApplies2 [s: Student, i: Internship] {
	#Student = 1
	#Internship = 1
	#Interview = 1
	(all iv: Interview | iv.application = none)
	i.iState = Open and
		(
			s.isHired = False and
			after (one a2: Application |
				getStudent[a2] = s and getInternship[a2] = i and a2.aState = Submitted and
			after (a2.aState = UnderReview and
			after (a2.aState = Accepted and
				(one iv2: Interview | iv2.application = a2 and iv2.state = Scheduled and
			after (iv2.state = Refused and s.isHired = False)))))
		)
}

//Student applies to an internship, his application is accepted and then he is hired after the interview
//then the intership is closed
pred studentApplies3 [s: Student, i: Internship] { //NON FUNZIONA
	#Student = 1
	#Internship = 1
	#Interview = 1
	(all iv: Interview | iv.application = none)
	i.iState = Open and	
	(
		s.isHired = False and
		after (one a3: Application |
			getStudent[a3] = s and getInternship[a3] = i and a3.aState = Submitted and
		after (a3.aState = UnderReview and
		after (a3.aState = Accepted and
			(one iv3: Interview | iv3.application = a3 and iv3.state = Scheduled and
		after (iv3.state = Hired and s.isHired = True and i.iState = Closed)))))
	)
}

pred world {
	#Student >= 2
	#Company >= 2
	#Internship >= 2
	#Application >= 1
	#Interview >= 1
	#Notification >= 1
}

/**********ASSERTION**********/

//Only student that uploaded their cv can be hired
assert hiredWithCV {
	all s: Student | s.isHired = True implies not(s.cv = none)
}

//Student can be hired only if he has been interviewed
assert hiredOnlyIfInterviewed {
	all s: Student | s.isHired = True iff
		(some i: Interview | getStudent[i.application] = s and i.state = Hired)
}

/**********COMMANDS**********/

run studentApplies1 for 5
run studentApplies2 for 5 but 10 steps
run studentApplies3 for 5 but 10 steps
run world for 5 but 10 steps

check hiredWithCV for 5
check hiredOnlyIfInterviewed for 5
