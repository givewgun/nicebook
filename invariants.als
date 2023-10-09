/*
	Team 10
*/
open Project_Sigs

// Ensures every User is part of a Nicebook instance.
pred userMustBeInAState {
	User = Nicebook.users
}

// Ensures users from different Nicebooks cannot be friends with each other.
pred userCannotBeFriendsWithOtherInDifferentState {
	all u1,u2: User | #(users.u1 & users.u2) = 0 implies (u2 not in u1.friends and u1 not in u2.friends)
}

// Ensures that a user is not friends with themselves.
pred notFriendsWithSelf[s: Nicebook] {
	all u: User | u not in u.friends
}

// Ensures that the friendship relationship is symmetric, i.e., if A is a friend of B, then B is a friend of A.
pred symmetricFriendship[s: Nicebook] {
	all u1,u2: User | u1 in u2.friends iff u2 in u1.friends
}

// Combines all user-related invariants.
pred userInvariants[s :Nicebook] {
	userCannotBeFriendsWithOtherInDifferentState  
	userMustBeInAState
	notFriendsWithSelf[s] 
	symmetricFriendship[s] 
}

// Ensures every piece of content is owned by at least one user across all states.
pred contentOwnedbyAtLeastOnceUserAcrossAllState[s: Nicebook] {
	all c: Content |  #(owns.c) > 0
}

// Ensures every piece of content is owned by only one user within a specific state.
pred contentOwnedbyOnlyOneUserInAState[s: Nicebook] {
	all c: Content | c in s.users.owns implies  #(owns.c & s.users) = 1
}

// Ensures that the comment content doesn't form a cyclic relation.
pred commentNotCyclic[s: Nicebook]{
	all cm: Comment | (cm not in cm.^attachedTo)
}

// Ensures a comment is attached to content that's published on the same wall as the owner.
pred commentNotAddedToUnpublisedContent[s: Nicebook]{
	all c, cm: Content | c in cm.attachedTo implies (cm in (owns.c).has.contains and c in (owns.c).has.contains)
}

// Ensures a comment is placed on the content owner's wall.
pred commentMustBeOnAContentOwnerWall[s: Nicebook]{
	//comment must be on the same wall as the content owner wall
	all c: Content, cm: Comment | (c not in Comment) implies cm in (owns.c).has.contains
}

// Ensures each comment in a wall is attached to a content in that wall.
pred commentMustBeAttachedToContentInEveryWallItIsIn[s: Nicebook] {
	all cm: Comment, w: Wall | cm in w.contains implies #(cm.attachedTo & w.contains) = 1
}

// Ensures every comment is on at least one wall across states.
pred commentMustBeOnAtLeastOneWallAcrossState[s: Nicebook] {
	all c: Comment |  #(contains.c) > 0
}

// Ensures every comment is on only one wall within a specific state.
pred commentMustBeOnOnlyOneWallinAState[s: Nicebook] {
	all c: s.users.owns |  c in Comment  implies #(contains.c & s.users.has) = 1
}

// Ensures every comment attached to a photo is in the same state as the photo.
pred commentMustBeAttachedToSameStateAsPhoto[s: Nicebook, p: Photo]{
	all cm: Comment | cm in ^attachedTo.p implies #(users.(owns.(cm.attachedTo)) & (users.owns.cm)) > 0
}

// Ensures every comment is attached to only one photo.
pred commentMustBeAttachedToOnePhoto[s: Nicebook]{
	all cm: Comment | #(cm.^attachedTo & Photo) = 1
}

// Grouping of all content-related invariants.
pred contentInvariant[s: Nicebook] {
	contentOwnedbyOnlyOneUserInAState[s] //
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

// Ensures every wall is associated with a user within a specific state.
pred wallHaveOneUserInAState[s: Nicebook] {
	all w: s.users.has |  #(has.w &  s.users) = 1
}


// Ensures every wall is associated with at least one user across all states.
pred wallOwnedbyAtLeastOneUserAcrossAllState[s: Nicebook] {
	all w: Wall |  #(has.w) > 0
}

// Grouping of all wall-related invariants.
pred wallInvariant[s: Nicebook] {
	wallHaveOneUserInAState[s] 
	wallOwnedbyAtLeastOneUserAcrossAllState[s]
}

// Ensure share privacy is being applied 
pred sharePrivacyInvariant[s: Nicebook, u1,u2:User,  p:Photo]{
	(u2 in (u1).friends and (owns.p).sharePrivacy != OnlyMe and p.viewPrivacy!=OnlyMe)
	or (u2 in (u1).friends.friends and (p.viewPrivacy=Everyone or p.viewPrivacy=FriendsOfFriends)
	and  ((owns.p).sharePrivacy=Everyone  or (owns.p).sharePrivacy=FriendsOfFriends))
}


// need check
// Ensure comment privacy is being applied 
pred commentPrivacyInvariant[s: Nicebook, u1,u2:User,  c1:Content]{
	(u2 in (u1).friends and (owns.c1).commentPrivacy != OnlyMe and c1.viewPrivacy!=OnlyMe)
	or (u2 in (u1).friends.friends and (c1.viewPrivacy=Everyone or c1.viewPrivacy=FriendsOfFriends)
	and  ((owns.c1).commentPrivacy=Everyone  or (owns.c1).commentPrivacy=FriendsOfFriends))
}



pred niceBookInvariants[s: Nicebook] {
	userInvariants[s]
	contentInvariant[s]
	wallInvariant[s]
	all u1,u2: User, p: Photo | (u1 != u2 and u2 in s.users and	u1 in s.users and p in u1.owns) implies sharePrivacyInvariant[s, u1,u2,p]
}
