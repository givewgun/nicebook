open Project_Sigs

pred userMustBeInAState {
	User = Nicebook.users
}

pred notFriendsWithSelf[s: Nicebook] {
	all u: User | u not in u.friends
}


pred symmetricFriendship[s: Nicebook] {
	all u1,u2: User | u1 in u2.friends iff u2 in u1.friends
}

// user invariants
pred userInvariants[s :Nicebook] {
	userMustBeInAState and
	notFriendsWithSelf[s] and 
	symmetricFriendship[s] 
//	all u1, u2: User | uniquePosts[u1, u2]
	//all u1, u2: User | cannotViewOthersPrivatePosts[u1, u2]
}

pred contentOwnedbyOnlyOneUser[s: Nicebook] {
	all c: s.users.owns | one (owns.c & s.users)
}

pred commentNotCyclic[s: Nicebook]{
	all cm: Comment | cm in Comment implies (cm not in cm.^attachedTo)
	
}

pred commentNotAddedToOtherUserUnpublisedContent[s: Nicebook]{
	//comment must be attached to published content on a wall if user is different 
	no u1,u2: User, c: Content, cm: Comment | 
		u2 != u1 and 
		c in u1.owns and
		c not in u1.has.contains and
		cm in u2.owns and 
		c in cm.attachedTo

}

pred commentMustBeOnAContentOwnerWall[s: Nicebook]{
	//comment must be on the same wall as the content owner wall
	all c, cm: Content | (c not in Comment) implies cm in (owns.c).has.contains

}

pred commentMustBeOnOneWall[s: Nicebook]{
	all cm: Comment | one contains.cm
}

pred contentInvariant[s: Nicebook] {
	contentOwnedbyOnlyOneUser[s] and
	commentNotCyclic[s] and
	commentNotAddedToOtherUserUnpublisedContent[s] and 
	commentMustBeOnAContentWall[s] and
	commentMustBeOnOneWall[s]
}

pred wallHaveOneUser[s: Nicebook] {
	all w: s.users.has | one (has.w &  s.users)
}

pred wallInvairant[s: Nicebook] {
	wallHaveOneUser[s]
}

pred niceBookInvariants[s: Nicebook] {
	userInvariants[s] and
	contentInvariant[s] and
	wallInvairant[s]
}
