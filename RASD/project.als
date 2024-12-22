enum ApplicationStatus {Submitted, UnderReview, Accepted, Rejected}
enum InternshipStatus {Open, Ongoing, Closed}
enum InterviewStatus{Scheduled, Hired, Refused}

enum Bool{True, False}

abstract sig CV {}
abstract sig User {}

sig Student extends User {
	cv: one CV, //We assume that the student has already uploaded his CV
	var isHired: one Bool
}

sig Company extends User {
	internships: set Internship
}

sig Internship {
    var iState: InternshipStatus,
} {one c: Company | this in c.internships}

sig Notification {
	between: Student -> Internship,
	notifiedCompany: one Company
} {
	getInternshipNotification[this] in notifiedCompany.internships
}

var sig Application {
    var aState: ApplicationStatus,
	var apply: Student -> Internship
} {
	(some s: Student, i: Internship | getStudent[this] = s and getInternship[this] = i)
}

var sig Interview {
	var application: one Application,
	var state: InterviewStatus
} {one a: Application | a.aState = Accepted and a in application}

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
		let s = getStudent[a] | #s = 1
}

//Every application is sent for one and only one internship
fact {
	all a: Application |
		let i = getInternship[a] | #i = 1
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
	all i: Interview | always (i.application' = i.application)
}

//Apply never changes -> RISCRIVI
fact {
	all a: Application | always(a.apply' = a.apply)
}

//The application discussed during the interview is unique
fact {
	always(all a: Application | lone i: Interview | i.application = a)
}

//Lifecycle of Internship
//... Open -> Ongoing -> Closed
fact {
	all i: Internship | 
		always (i.iState = Open implies eventually i.iState = Ongoing
				and i.iState = Ongoing implies eventually closeInternship[i])
				//and i.iState = Closed implies after always i.iState = Closed)
}

//Lifecycle of Application
//... Submitted -> UnderReview -> Accepted or Rejected
fact{
	all a: Application | 
		always (a.aState = Submitted implies
				(historically a.aState = Submitted) and
				(eventually a.aState = UnderReview))
}

fact{
	all a: Application | 
		always (a.aState = Accepted implies
				(historically a.aState = UnderReview) and
				(after always a.aState = Accepted))
}

fact{
	all a: Application | 
		always (a.aState = Rejected implies
				(historically a.aState = UnderReview) and
				(after always a.aState = Rejected))
}

//Lifecycle of Interview
// ... -> Scheduled -> Hired or Refused

fact {
	all i: Interview |
		always (i.state = Refused implies
				(historically i.state = Scheduled) and
				(after always i.state = Refused))
}

fact {
	all i: Interview |
		always (i.state = Hired implies
				(historically i.state = Scheduled) and
				(after always i.state = Hired))
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
	all s: Student | s.isHired = True iff
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

/*
PROBLEMI:
	1) Interview hired e student non hired -> succede perchè eventually student può tornare non hired
	2) Non esistono interview
	3) Esistono interview per application in UnderReview o Submitted
	4) Student passa ad Hired anche senza interview
*/

/**********PREDICATES**********/

pred closeInternship[i: Internship] {
	i.iState = Closed and getCompany[i].internships' = getCompany[i].internships - i
}

//  -> Cambia nome
pred test [s: Student, i: Internship]{
		historically(no Application and #Internship = 1 and #Student = 1)and
		after(one a2: Application | getStudent[a2] = s and getInternship[a2] = i and a2.aState = Submitted and
			after(a2.aState = UnderReview and after(a2.aState = Accepted and i.iState = Ongoing and
				one iv: Interview | iv.state = Scheduled and after(iv.state = Hired and
					s.isHired = True and i.iState = Closed))))
}

//Student submit an application for an internship -> NON VA
pred submitApplication [s: Student, i: Internship] {
	//Precondition
	historically(no a1: Application | getStudent[a1] = s and getInternship[a1] = i) implies
	//Postcondition
	eventually(one a2: Application | getStudent[a2] = s and getInternship[a2] = i)
}

// Student can search for open or ongoing internships
pred searchInternship[s: Student] {
	some i: Internship | i.iState = Open or i.iState = Ongoing
}

pred world {
	#Student >= 2
	#Company > 2
	#Internship >= 2
	#Notification >= 1
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
pred a[s: Student] {
	s.isHired = True
}

run test for 5 but 10 steps

run world for 5 but 10 steps
run submitApplication for 5

check hiredWithCV for 5
check interviewIfAccepted for 5
check everyInternshipBelong for 3 but 1 Company
