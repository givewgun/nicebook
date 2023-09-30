sig User {
	friends: set User,
	owns: some Content,
	has: one Wall,
}

sig Wall {
	has: some PublishedContent
}

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



sig NiceBook {
	// relations 
}

sig PublishedContent in Content {}

abstract sig PrivacySetting {}

sig Everyone, OnlyMe, Friends,  FriendsOfFriends extends PrivacySetting {}

