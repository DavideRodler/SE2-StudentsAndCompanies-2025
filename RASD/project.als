enum ApplicationStatus {Submitted, UnderReview, Accepted, Rejected}
enum InternshipStatus {Open, Ongoing, Closed}
enum InterviewStatus{Scheduled, Hired, Refused}

enum Bool{True, False}

abstract sig User {}

sig Student extends User {
	cv: lone CV,
	var isHired: one Bool
}

sig Company extends User {
	internships: set Internship
}

sig Application {
    var aState: ApplicationStatus,
	apply: Student -> Internship
} {one i: Interview | this in i.application}

sig Internship {
    var iState: InternshipStatus,
} {one c: Company | this in c.internships}

sig Interview {
	application: one Application,
	internship: one Internship,
	var state: InterviewStatus
}

var sig Notification { //Da mettere constraint per evitare che between e notifiedCompany cambino a caso
	var between: Student -> Internship,
	var notifiedCompany: one Company
}

//DA COMPLETARE
sig Match{
	//PER ORA INUTILIZZATO
}

sig Feedback{} //PER ORA INUTILIZZATO

abstract sig CV {}

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

/**********FACTS**********/

//Two students cannot have the same CV
fact {
	all disj s1, s2: Student | not (s1.cv = s2.cv) or (s1.cv = s2.cv and s1.cv = none) 
}

//Every application belong to one and only one student
fact{
	all a: Application |
		let s = getStudent[a] | #s = 1
}

//Every application is sent for one and only one internship
fact {
	all a: Application |
		let i = getInternship[a] | #i = 1
}

//Every notification is sent to one and only one student
fact {
	all n: Notification |
		let s = getNotifiedStudent[n] | #s = 1
}

//Every application is about one and only one internship
fact {
	all n: Notification |
		let i = getInternshipNotification[n] | #i = 1
}

//Lifecycle of Internship
//... Open -> Ongoing -> Closed
fact {
	all i: Internship | 
		always (i.iState = Open implies eventually i.iState = Ongoing
				and i.iState = Ongoing implies eventually i.iState = Closed
				and i.iState = Closed implies after always i.iState = Closed)
}

//Lifecycle of Application
//... Submitted -> UnderReview -> Accepted or Rejected
fact {
	all a: Application|
		always(a.aState = Submitted implies 
					eventually a.aState = UnderReview 
				and a.aState = UnderReview implies 
					eventually a.aState = Accepted or a.aState = Rejected
				and a.aState = Accepted implies 
					after always a.aState = Accepted
				and a.aState = Rejected implies 
					after always a.aState = Rejected)
}

//Lifecycle of Interview
// ... -> Scehduled -> Hired or Refused
fact {
	all i: Interview |
		always (i.state = Scheduled implies 
					eventually i.state = Hired or i.state = Refused
				and i.state = Hired implies
					after always i.state = Hired
				and i.state = Refused implies
					after always i.state = Refused)
}

//Lifecycle of Student -> TO BE CHECKED
// ... -> Unemployed -> Hired
fact {
	all s: Student | 
		always (s.isHired = True implies historically s.isHired = False and
			(eventually s.isHired = False or after always s.isHired = True))
}


//Student can apply only to open or ongoing internships -> Checked
fact {
	all a: Application |
		always (a.aState = Submitted
			implies getInternship[a].iState = Open or getInternship[a].iState = Ongoing)
}

//Student cannot apply twice to the same internship
fact{
	no disj a1, a2: Application | getStudent[a1] = getStudent[a2] and 
		getInternship[a1] = getInternship[a2] 
}

//Interviews cannot be scheduled if the application has not been accepted
fact {
	all a: Application | not (a.aState = Accepted) implies 
		no i: Interview | a in i.application
}

//If student is hired than his application is in Accepted state -> Checked
fact {
	all i: Interview | i.state = Hired implies i.application.aState = Accepted
}

//If a student is Refused than his application is in Rejected state -> Checked
fact {
	all i: Interview | i.state = Refused implies i.application.aState = Rejected
}

//Student is hired if and only if interview is in Hired state and isHired is true -> RISCRIVI MEGLIO -> Checked
fact {
	all i: Interview | i.state = Hired iff getStudent[i.application].isHired = True
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
	no disj n1, n2: Notification | getNotifiedStudent[n1] = getNotifiedStudent[n2] and
		getInternshipNotification[n1] = getInternshipNotification[n2]
}

/*
PROBLEMI:
	
*/


/**********PREDICATES**********/
// Predicate to describe when an application can be accepted

// Student can search for open or ongoing internships
pred searchInternship[s: Student] {
	some i: Internship | i.iState = Open or i.iState = Ongoing
}

// Students can submit application to one internship
pred submitApplication[s: Student, i: Internship] {
    some a: Application | getStudent[a] = s and getInternship[a] = i
}

pred world {
	#Student >= 2
	#Company > 2
	let  i = #Internship | i >= 2 and #Application <= i
}

/**********ASSERTION**********/

//Every internship belongs to a company -> si può fare di meglio
assert everyInternshipBelong {
	all i: Internship |
		some c: Company | i in c.internships
}

//Only student that uploaded their cv can be hired
assert hiredWithCV {
	all s: Student | s.isHired = True implies not(s.cv = none)
}

//Interview scheduled when application is accepted
assert interviewIfAccepted {
	//SCRIVERE MEGLIO
	all i: Interview | i.application.aState = Accepted
}

/**********COMMANDS**********/

//PREDICATO DI TEST DA TOGLIERE PRIMA DI CONSEGNARE
pred a [a: Application]{
	a.aState = Accepted and 
	(no i: Interview | a in i.application)
}

run a for 10

run world for 5

check hiredWithCV for 5
check interviewIfAccepted for 5
check everyInternshipBelong for 3 but 1 Company
