sig Nicebook {
	users : some User
}

sig User {
	friends: set User,
	owns: some Content,
	has: one Wall,
 	sharePrivacy : one PrivacySetting,
	// viewPrivacy: one PrivacySetting,
}

sig Wall {
	contains: some Content
}


abstract sig Content {
	viewPrivacy: one PrivacySetting,
	commentPrivacy: one PrivacySetting,
}

sig Photo extends Content {
 	// sharePrivacy : one PrivacySetting,
}

sig Comment extends Content {
	attachedTo: one Content,
}

abstract sig PrivacySetting {}

one sig Everyone, OnlyMe, Friends,  FriendsOfFriends extends PrivacySetting {}

