sig Nicebook {
	Friendship: User -> User,
	UserHasWall: User -> one Wall,
	UserOwnsContent: User -> some Content,
	WallContainsContent: Wall -> Content,
	CommentPrivacy: Content -> one PrivacySetting,
	ViewPrivacy: Content -> one PrivacySetting,
	CommentAttachedToContent: Comment -> one Content,
	SharePrivacy: Photo -> one PrivacySetting
}

sig User {
	friends: set User,
	owns: some Content,
	has: one Wall,
}

sig Wall {
	contains: some Content
}


abstract sig Content {
	viewPrivacy: one PrivacySetting,
	commentPrivacy: one PrivacySetting,
}

sig Photo extends Content {
 	sharePrivacy : one PrivacySetting,
}

sig Comment extends Content {
	attachedTo: one Content,
}

abstract sig PrivacySetting {}

sig Everyone, OnlyMe, Friends,  FriendsOfFriends extends PrivacySetting {}

