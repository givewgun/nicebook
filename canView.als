open Project_Sigs

fun canView(user: User): set Content {
  // Determine the content that the given 'user' can view based on different privacy settings.

  // Content with "OnlyMe" privacy setting: Only the owner of the content can view it.
  {c: Content | c.viewPrivacy = OnlyMe and c in user.owns} +

  // Content with "Friends" privacy setting: Either the owner or their direct friends can view it.
  {c: Content | c.viewPrivacy = Friends and (c in user.owns or c in user.friends.owns)} +

  // Content with "FriendsOfFriends" privacy setting: The owner, their direct friends, 
  // or friends of their friends can view it.
  {c: Content | c.viewPrivacy = FriendsOfFriends and 
      (c in user.owns or c in user.friends.owns or c in user.friends.friends.owns)} +

  // Content with "Everyone" privacy setting: Any user in the system can view it.
  {c: Content | c.viewPrivacy = Everyone}
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
		(content.viewPrivacy = OnlyMe implies content in user.owns) and
		
		// If the content's privacy is set to "Friends", then either the owner or their friends should be able to view it.
		(content.viewPrivacy = Friends implies (content in user.owns or content in user.friends.owns)) and
		
		// If the content's privacy is set to "FriendsOfFriends", then the owner, their friends, or their friends' friends should be able to view it.
		(content.viewPrivacy = FriendsOfFriends implies 
					(content in user.owns or content in user.friends.owns or content in user.friends.friends.owns)) 

		// If the content's privacy is set to "Everyone", then any user can view it.
  )
}

check NoPrivacyViolation for 5

run showScenario for 5 
