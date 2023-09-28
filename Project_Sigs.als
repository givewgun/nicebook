sig User {
	friends: set User,
	owns: some Content,
	has: one Wall,
}

sig Wall {}


abstract sig Content {
	viewPrivacy: one PrivacySetting,
	commentPrivacy: one PrivacySetting,
}

sig Photo extends Content {
 	sharePrivacy : one PrivacySetting,
}

sig Comment extends Content {
	attchedTo: one Content,
}



sig PublishedContent in Content {}

abstract sig PrivacySetting {}

sig Everyone, OnlyMe, Friends,  FriendsOfFriends extends PrivacySetting {}



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


run {
	all u: User | userInvariants[u]	
} for 2 but exactly 2 User

