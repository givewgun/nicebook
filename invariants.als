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

pred contentNotOwnByTwoUser[u1,u2: User, c: Content] {
	not (u1 != u2 and c in u1.owns and c in u2.owns)
}

pred commentNotCyclic[cm: Comment]{
	cm not in cm.^attchedTo
}

pred contentInvariant[c: Content] {
	all u1,u2:User | contentNotOwnByTwoUser[u1,u2,c] and
	commentNotCyclic[c]
}

pred niceBookInvariants {
	all u: User | userInvariants[u] and
	all c: Content | contentInvariant[c]
}
