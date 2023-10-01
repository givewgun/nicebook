open Project_Sigs

pred notFriendsWithSelf[u: User] {
//    	u not in u.friends
	no u: User | u in u.friends
}


pred symmetricFriendship[u1, u2: User] {
    u1 in u2.friends iff u2 in u1.friends
}

// user invariants
pred userInvariants[u: User] {
	all u: User | notFriendsWithSelf[u] 
	all u1, u2 : User | symmetricFriendship[u1, u2]
//	all u1, u2: User | uniquePosts[u1, u2]
	//all u1, u2: User | cannotViewOthersPrivatePosts[u1, u2]
}

pred contentOwnedbyOnlyOneUser[c: Content] {
	one owns.c
}

pred contentNotOwnByTwoUser[u1,u2: User, c: Content] {
	not (u1 != u2 and c in u1.owns and c in u2.owns)
}

pred commentNotCyclic[cm: Comment]{
	cm not in cm.^attchedTo
}

pred commentNotAddedToOtherUserUnpublisedContent[c: Content]{
	//comment must be attached to published content on a wall if user is different 
	no u1,u2: User, cm: Comment | (c in cm.attchedTo) and (u1 != u2) and (cm in u1.owns) and (c not in u2.has.contains) 

}

pred commentMustBeOnAContentWall[c: Content]{
	//comment must be on the same wall as the content
	all cm: Comment | cm in (contains.c).contains
}

pred commentMustBeOnOneWall[cm: Comment]{
	one contains.cm
}

pred contentInvariant[c: Content] {
	contentOwnedbyOnlyOneUser[c] and
	all u1,u2: User | contentNotOwnByTwoUser[u1,u2,c] and
	commentNotCyclic[c] and
	commentNotAddedToOtherUserUnpublisedContent[c] and 
	commentMustBeOnAContentWall[c] and
	all cm: Comment | commentMustBeOnOneWall[cm]
}

pred wallHaveOneUser[w: Wall] {
	one has.w
}

pred wallInvairant[w: Wall] {
	wallHaveOneUser[w]
}

pred niceBookInvariants {
	all u: User | userInvariants[u] and
	all c: Content | contentInvariant[c] and
	all w: Wall | wallInvairant[w]
}
