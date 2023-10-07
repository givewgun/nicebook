// A signature representing the entire social network "Nicebook."
sig Nicebook {
	users : some User  // Set of all users in the Nicebook.
}

// A signature representing an individual user in the Nicebook.
sig User {
	friends: set User,            // Set of friends for the user.
	owns: some Content,           // Content owned by the user.
	has: one Wall,                // Wall associated with the user.
	sharePrivacy : one PrivacySetting, // Privacy setting that controls who can share the user's content.
	viewPrivacy: one PrivacySetting    // Privacy setting that controls who can view the user's content.
}

// A signature representing a user's wall which contains content.
sig Wall {
	contains: some Content  // Set of content displayed on the wall.
}

// An abstract signature representing any type of content (either photo or comment).
abstract sig Content {
	commentPrivacy: one PrivacySetting  // Privacy setting controlling who can comment on the content.
}

// A signature representing photos, which extends the abstract Content signature.
sig Photo extends Content {}

// A signature representing comments, which extends the abstract Content signature.
sig Comment extends Content {
	attachedTo: one Content  // The content (e.g., photo) to which the comment is attached.
}

// An abstract signature representing different privacy settings.
abstract sig PrivacySetting {}

// Concrete privacy settings. Each content can have one of these privacy settings.
one sig Everyone, OnlyMe, Friends,  FriendsOfFriends extends PrivacySetting {}
