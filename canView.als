open Project_Sigs

fun canView(user: User): set Content {
	// This function determines which content a specific user can view based on privacy settings.
	
	// Content with "OnlyMe" privacy setting:
	// Only the owner of the content can view it, and it must be on a wall.
	{c: Content | (owns.c).viewPrivacy = OnlyMe and c in user.owns} +

	// Content with "Friends" privacy setting:
	// Either the owner or their direct friends can view it, and it must be on a wall.
	{c: Content | (owns.c).viewPrivacy = Friends and (c in user.owns or c in user.friends.owns) and some w: Wall | c in w.contains} +

	// Content with "FriendsOfFriends" privacy setting:
	// The owner, their direct friends, or friends of their friends can view it, 
	// and it must be on a wall.
	{c: Content | (owns.c).viewPrivacy = FriendsOfFriends and 
			(c in user.owns or c in user.friends.owns or c in user.friends.friends.owns) and some w: Wall | c in w.contains} +

	// Content with "Everyone" privacy setting:
	// Any user in the system can view it, and it must be on a wall.
	{c: Content | (owns.c).viewPrivacy = Everyone and some w: Wall | c in w.contains}
}

pred showScenario {
	some u: User | 
	#canView[u] > 0 // This ensures that there's at least one content viewable by the user 'u'
}

assert NoPrivacyViolation {
	// For every user and piece of content that the user can view,
	// ensure that the viewing is in accordance with the content's privacy setting.
	all user: User, content: Content | content in canView[user] implies (

		// If the content's privacy is set to "OnlyMe", then only the owner should be able to view it.
		((owns.content).viewPrivacy = OnlyMe implies content in user.owns) and
		
		// If the content's privacy is set to "Friends", then either the owner or their friends should be able to view it.
		((owns.content).viewPrivacy = Friends implies (content in user.owns or content in user.friends.owns)) and
		
		// If the content's privacy is set to "FriendsOfFriends", then the owner, their friends, or their friends' friends should be able to view it.
		((owns.content).viewPrivacy = FriendsOfFriends implies 
			(content in user.owns or content in user.friends.owns or content in user.friends.friends.owns)) 

		// If the content's privacy is set to "Everyone", then any user can view it.
  )
}

check NoPrivacyViolation for 5

run showScenario for 5 


fun canView1(s: Nicebook, user: User): set Content {
	// This function determines which content a specific user can view based on privacy settings and the current Nicebook state.

	// Content with "OnlyMe" privacy setting:
	// Only the owner of the content can view it.
	{c: Content | c in s.users.owns and (owns.c).viewPrivacy = OnlyMe and c in user.owns} +

	// Content with "Friends" privacy setting:
	// Either the owner or their direct friends can view it, and it must be on a wall.
	{c: Content | c in s.users.owns and (owns.c).viewPrivacy = Friends and (c in user.owns or c in user.friends.owns) and some w: Wall | c in w.contains} +

	// Content with "FriendsOfFriends" privacy setting:
	// The owner, their direct friends, or friends of their friends can view it, 
	// and it must be on a wall.
	{c: Content | c in s.users.owns and (owns.c).viewPrivacy = FriendsOfFriends and 
		(c in user.owns or c in user.friends.owns or c in user.friends.friends.owns) and some w: Wall | c in w.contains} +

	// Content with "Everyone" privacy setting:
	// Any user in the system can view it, and it must be on a wall.
	{c: Content | c in s.users.owns and (owns.c).viewPrivacy = Everyone and some w: Wall | c in w.contains}
}

assert NoPrivacyViolation1 {
	all s: Nicebook, user: User, c: Content | 
		c in canView1[s, user] implies
			// For the OnlyMe privacy setting
			(c in user.owns and (owns.c).viewPrivacy = OnlyMe) or
			// For the Friends privacy setting
			(c in user.owns or c in user.friends.owns and (owns.c).viewPrivacy = Friends) or
			// For the FriendsOfFriends privacy setting
			(c in user.owns or c in user.friends.owns or c in user.friends.friends.owns and (owns.c).viewPrivacy = FriendsOfFriends) or
			// For the Everyone privacy setting
			(c in s.users.owns and (owns.c).viewPrivacy = Everyone)
}

check NoPrivacyViolation1 for 5

