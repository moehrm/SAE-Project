/*
 * Signatures
 *
 * Your model should contain the following (and potentially other) signatures.
 * If necessary, you have to make some of the signatures abstract and
 * make them extend other signatures.
 */

//// Athlete
abstract sig Athlete { }
sig MaleAthlete extends Athlete { }
sig FemaleAthlete extends Athlete { }

fact athleteFacts {
	// Every Athlete is citizen of some country (countries).
	all athlete: Athlete | some country: Country | athlete in country.athletes
	// Every Athlete is member of some team.
	all athlete: Athlete | some team: Team | athlete in team.athletes
	// Athlete and belonging team should represent same country.
	all athlete: Athlete, team: Team | some country: Country | athlete in team.athletes 
		iff athlete in country.athletes && team in country.teams 
	// Athelte only belong to one team for one event.
	all event: Event, disj t1, t2: event.teams, athlete: t1.athletes | not athlete in t2.athletes
}

////Country
sig Country {
	athletes: some Athlete,
	teams: set Team
}

fact countryFacts {
	all c: Country, team: c.teams | team.country = c
	// Each country sends one team for one event.
	all event: Event, disj t1, t2: event.teams | t1.country != t2.country
}

//// Discipline
sig Discipline {
	events: some Event
}

fact disciplineFacts {
	// Each event is for only one discipline.
	all disj d1, d2: Discipline, event: d1.events | not event in d2.events
	// Each event is owned by a discipline.
	all event: Event | some discipline: Discipline | event in discipline.events
}


//// Event
sig Event {
	phases: some Phase,
	goldMedals: some GoldMedal,
	silverMedals: set SilverMedal,
	bronzeMedals: set BronzeMedal,
	teams: some Team
}

fact eventFacts {
	// Each phase is for only one event.
	all disj e1, e2: Event, phase: e1.phases | not phase in e2.phases
	// Each phase is owned by an event.
	all phase: Phase | some event: Event | phase in event.phases
	// Each event has more than 3 teams.
	all event: Event | 3 <= #event.teams
	// Each event has more than 3 but less than or equal to #teams medals.
	all event: Event | 3 <= #event.getMedals && #event.getMedals <= #event.teams
}

fact medalDistributionRules {
	// If #goldMedals >= 3, no silver or bronze medals.
	all event: Event | #event.silverMedals = 0 && #event.bronzeMedals = 0 iff 3 <= #event.goldMedals
	// If #goldMedals > 1, no silver medals.
	all event: Event | #event.silverMedals = 0 iff 1 < #event.goldMedals
	// If #goldMedals = 1 and #silverMedals > 1, no bronze medals.
	all event: Event | #event.bronzeMedals = 0 iff 1 < #event.silverMedals && 1 = #event.goldMedals
}

//// Location	
sig Location {

}

fact locationFacts {
	// Each location is owned by some performances.
	all l: Location | some performance: Performance | l in performance.location
}

//// Medal
abstract sig Medal {
	team: one Team,
	event: one Event
}
sig GoldMedal extends Medal { }
sig SilverMedal extends Medal { }
sig BronzeMedal extends Medal { }

fact medalFacts {
	// Medal belongs to a team participating in the event.
	all medal: Medal, e: Event | medal in e.getMedals iff medal.event = e && medal.team in e.teams
	// One medal in for one event belongs to only one team.
	all disj m1, m2: Medal | m1.event = m2.event => m1.team != m2.team
}

//// Performance
sig Performance { 
	score: one Score,
	startTime: one Time,
	endTime: one Time,
	location: one Location,
	teams: some Team
} 

fact performanceFacts {
	// For each performance, startTime is before endTime.
	all performance: Performance | isBefore[performance.startTime, performance.endTime] 
	// Given this start-end time period, only this performance can occur at this location.
	all disj pf1, pf2: Performance | not (isBefore[pf1.endTime, pf2.startTime] or isBefore[pf2.endTime, pf1.startTime])
		=> pf1.location != pf2.location
	// Teams participate in performances belongs to the event.
	all event: Event | event.teams = event.getPhases.getPerformances.getParticipants
}

//// Phase
sig Phase { 
	performances: some Performance,
	nextPhase: lone Phase
}

fact phaseFacts {
	// Each performance is for only one phase.
	all disj ph1, ph2: Phase, performance: ph1.performances | not performance in ph2.performances
	// Each performance is owned by one phase.
	all performance: Performance | some phase: Phase | performance in phase.performances
	// A phase is not its own next phase.
	all phase: Phase | not phase in phase.^nextPhase
	// Phases in one event are connected.
	all event: Event, disj ph1, ph2: event.phases | phaseIsBefore[ph1,ph2] or  phaseIsBefore[ph2,ph1]
}

//// Score
sig Score { }

fact scoreFact {
	// Each score is only for one performance.
	all disj pf1, pf2: Performance, s: pf1.score | not s in pf2.score
	// Each score is owned by a performance.
	all s: Score | some performance: Performance | s in performance.score
}

//// Team
sig Team { 
	athletes: some Athlete,
	country: one Country
}

fact teamFacts {
	// Each team is owned by some event.
	all team: Team | some event: Event | team in event.teams
}

//// Time
sig Time { 
	next: lone Time
}

fact timeFacts {
	// Time is connected
	all disj t1, t2: Time | isBefore[t1, t2] or isBefore[t2,t1]
	// A Time is not its own next Time.
	all time: Time | not time in time.^next
	// Each time is owned by some performance.
	all time: Time | some performance: Performance | time = performance.startTime 
		or time = performance.endTime
}

/*
 * Predicates
 */

// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] { 
	t1 != t2 && t2 in t1.^next
}

// True iff p1 is strictly before p2.
pred phaseIsBefore[p1, p2: Phase] { 
	p1 != p2 && p2 in p1.^nextPhase
}

// True iff m is a gold medal.
pred isGoldMedal[m : Medal] { 
	m in GoldMedal
}

// True iff m is a silver medal.
pred isSilverMedal[m : Medal] {
	m in SilverMedal
}

// True iff m is a bronze medal.
pred isBronzeMedal[m: Medal] {
	m in BronzeMedal
}

// True iff t is among the best teams in phase p.
pred isAmongBest[t: Team, p: Phase] {  }

/*
 * Functions
 */

// Returns all the events offered by the discipline d.
fun getEvents[d: Discipline] : set Event { 
	d.events
} 

// Returns all the teams which participate in the event e.
fun getEventParticipants[e: Event] : set Team { 
	e.teams
}

// Returns all the phases of the event e.
fun getPhases[e: Event] : set Phase {
	e.phases
}

// Returns all the performances which take place within the phase p.
fun getPerformances[p: Phase] : set Performance {
	p.performances
}

// Returns the set of medals handed out for the event e.
fun getMedals[e: Event] : set Medal {
	e.goldMedals + e.silverMedals + e.bronzeMedals
}

// Returns the start time of the performance p.
fun getStart[p : Performance] : Time {
	p.startTime
}

// Returns the end time of the performance p.
fun getEnd[p: Performance] : Time {
	p.endTime
}

// Returns the location of the performance p.
fun getLocation[p: Performance] : Location { 
	p.location
} 

// Returns all the teams which paricipate in the performance p.
fun getParticipants[p: Performance] : set Team {
	p.teams
}

// Returns all the athletes which belong to the team t.
fun getMembers[t: Team] : set Athlete { 
	t.athletes
}

// Returns the team which won the medal m.
fun getWinner[m: Medal] : Team {
	m.team
}

run { #Discipline = 2 
	and #Performance = 2
	and #Country = 3
  and #Time = 3
 	and #Location = 2} for 10
