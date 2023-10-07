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
	userCannotBeFriendsWithOtherInDifferentState  
	userMustBeInAState
	notFriendsWithSelf[s] 
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
	all cm: Comment | (cm not in cm.^attachedTo)
}

pred commentNotAddedToUnpublisedContent[s: Nicebook]{
	all c, cm: Content | c in cm.attachedTo implies (cm in (owns.c).has.contains and c in (owns.c).has.contains)
}

pred commentMustBeOnAContentOwnerWall[s: Nicebook]{
	//comment must be on the same wall as the content owner wall
	all c, cm: Content | (c not in Comment) implies cm in (owns.c).has.contains
}

pred commentMustBeAttachedToContentInEveryWallItIsIn[s: Nicebook] {
	all cm: Comment, w: Wall | cm in w.contains implies #(cm.attachedTo & w.contains) = 1
}



pred commentMustBeOnAtLeastOneWallAcrossState[s: Nicebook] {
	all c: Comment |  #(contains.c) > 0
}

pred commentMustBeOnOnlyOneWallinAState[s: Nicebook] {
	all c: s.users.owns |  c in Comment  implies #(contains.c & s.users.has) = 1
}


pred commentMustBeAttachedToSameStateAsPhoto[s: Nicebook, p: Photo]{
	all cm: Comment | cm in ^attachedTo.p implies #(users.(owns.(cm.attachedTo)) & (users.owns.cm)) > 0
}

pred commentMustBeAttachedToOnePhoto[s: Nicebook]{
	all cm: Comment | #(cm.^attachedTo & Photo) = 1
}

pred contentInvariant[s: Nicebook] {
	contentOwnedbyOnlyOneUserInAState[s]
	contentOwnedbyAtLeastOnceUserAcrossAllState[s] 
	all p: Photo | commentMustBeAttachedToSameStateAsPhoto[s,p]  
	commentNotCyclic[s] 
	commentNotAddedToUnpublisedContent[s]  
	commentMustBeOnAContentOwnerWall[s] 
	commentMustBeOnAtLeastOneWallAcrossState[s] 
	commentMustBeOnOnlyOneWallinAState[s]
	commentMustBeAttachedToOnePhoto[s]
	commentMustBeAttachedToContentInEveryWallItIsIn[s]
}

pred wallHaveOneUserInAState[s: Nicebook] {
	all w: s.users.has |  #(has.w &  s.users) = 1
}

pred wallInvariant[s: Nicebook] {
	wallHaveOneUserInAState[s] 
	wallOwnedbyAtLeastOneUserAcrossAllState[s]
}

pred wallOwnedbyAtLeastOneUserAcrossAllState[s: Nicebook] {
	all w: Wall |  #(has.w) > 0
}


pred niceBookInvariants[s: Nicebook] {
	userInvariants[s]
	contentInvariant[s]
	wallInvariant[s]
}
