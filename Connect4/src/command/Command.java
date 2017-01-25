package command;

public abstract class Command {

	public final String keyword;
	
	public Command(String keyword) {
		this.keyword = keyword;
	}
	
	abstract public String usage();
	public int keywordLength() {
		return keyword.length();
	}

}
