open Project_Sigs

pred userMustBeInAState {
	User = Nicebook.users
}

pred userCannotBeFriendsWithOtherInDifferentState {
	all u1,u2: User | #(users.u1 & users.u2) = 0 implies (u2 not in u1.friends and u1 not in u2.friends)
}


pred notFriendsWithSelf[s: Nicebook] {
	all u: User | u not in u.friends
}

pred symmetricFriendship[s: Nicebook] {
	all u1,u2: User | u1 in u2.friends iff u2 in u1.friends
}

// user invariants
pred userInvariants[s :Nicebook] {
	userCannotBeFriendsWithOtherInDifferentState and 
	userMustBeInAState and
	notFriendsWithSelf[s] and 
	symmetricFriendship[s] 
//	all u1, u2: User | uniquePosts[u1, u2]
	//all u1, u2: User | cannotViewOthersPrivatePosts[u1, u2]
}

pred contentOwnedbyAtLeastOnceUserAcrossAllState[s: Nicebook] {
	all c: Content |  #(owns.c) > 0
}

pred contentOwnedbyOnlyOneUserInAState[s: Nicebook] {
	all c: s.users.owns |  #(owns.c & s.users) = 1
}

pred commentNotCyclic[s: Nicebook]{
	all cm: Comment | (cm not in cm.^attachedTo) and (cm not in ^attachedTo.cm)
}

pred commentNotAddedToUnpublisedContent[s: Nicebook]{
	//comment must be attached to published content on a wall if user is different 
	no u1,u2: User, c: Content, cm: Comment | 
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

pred commentMustBeAttachedToSameStateAsPhoto[s: Nicebook, p: Photo]{
	all cm: Comment | cm in ^attachedTo.p implies #(users.(owns.(cm.attachedTo)) & (users.owns.cm)) > 0
}

pred commentMustBeAttachedToOnePhoto[s: Nicebook]{
	all cm: Comment | #(cm.^attachedTo & Photo) = 1
}

pred contentInvariant[s: Nicebook] {
	contentOwnedbyOnlyOneUserInAState[s] and
	contentOwnedbyAtLeastOnceUserAcrossAllState[s] and
	all p: Photo | commentMustBeAttachedToSameStateAsPhoto[s,p] and 
	commentNotCyclic[s] and
	commentNotAddedToUnpublisedContent[s] and 
	commentMustBeOnAContentOwnerWall[s] and
	commentMustBeOnOneWall[s] and 
	commentMustBeAttachedToOnePhoto[s]
}

pred wallHaveOneUserInAState[s: Nicebook] {
	all w: s.users.has |  #(has.w &  s.users) = 1
}

pred wallInvairant[s: Nicebook] {
	wallHaveOneUserInAState[s] and 
	wallOwnedbyAtLeastOneUserAcrossAllState[s]
}

pred wallOwnedbyAtLeastOneUserAcrossAllState[s: Nicebook] {
	all w: Wall |  #(has.w) > 0
}


pred niceBookInvariants[s: Nicebook] {
	userInvariants[s] and
	contentInvariant[s] and
	wallInvairant[s]
}
