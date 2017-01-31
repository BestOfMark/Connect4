package client.ui;

import java.awt.BorderLayout;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.util.Observable;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import javax.print.attribute.standard.JobPriority;
import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JTextPane;

import client.Client;

public class GUI extends View implements ActionListener {

	private JFrame frame;
	private JTextArea fieldArea;
	private JTextArea internMessages;
	private JTextArea chatMessages;
	private JTextField outwardChat;
	private JButton sendChat;
	private JButton gameStart;
	
	public GUI(Client client) {
		super(client);
		frame = new JFrame("Connect4 GUI");
		frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		
		JPanel div = new JPanel(new BorderLayout());
		JPanel p1 = new JPanel();
		p1.setBorder(BorderFactory.createTitledBorder("Field"));
		fieldArea = new JTextArea(10, 50);
		p1.add(fieldArea);
		div.add(BorderLayout.NORTH, p1);
		
		JPanel p2 = new JPanel();
		p2.setBorder(BorderFactory.createTitledBorder("Console"));
		internMessages = new JTextArea(10, 50);
		p2.add(internMessages);
		div.add(BorderLayout.SOUTH, p2);
		
		JPanel p3 = new JPanel(new BorderLayout());
		p3.setBorder(BorderFactory.createTitledBorder("Chat"));
		chatMessages = new JTextArea(21, 30);
		outwardChat = new JTextField();
		sendChat = new JButton("Send");
		sendChat.addActionListener(this);
		p3.add(BorderLayout.NORTH, chatMessages);
		p3.add(BorderLayout.CENTER, outwardChat);
		p3.add(BorderLayout.EAST, sendChat);

		gameStart = new JButton("New game");
		gameStart.addActionListener(this);
		gameStart.setEnabled(true);
		
		frame.add(BorderLayout.CENTER, div);
		frame.add(BorderLayout.EAST, p3);
		frame.add(BorderLayout.SOUTH, gameStart);
		
		frame.pack();
		frame.setVisible(true);
	}

	@Override
	public void update(Observable o, Object arg) {
		fieldArea.setText(o.toString());
		if (arg != null && arg.equals("START")) {
			gameStart.setEnabled(false);
		} else if (arg != null && arg.equals("END")) {
			gameStart.setEnabled(true);
		}
	}

	@Override
	public void userInput(String input) {
		//Do nothing
	}

	@Override
	public void internalMessage(String msg) {
		internMessages.append(msg + "\n");
	}

	@Override
	public void chatMessage(String msg) {
		chatMessages.append(msg + "\n");
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		if (e.getSource() == gameStart) {
			try {
				client.getProtocoller().cmdGameRequest();
				internalMessage("Game request sent");
			} catch (IOException e1) {
				internalMessage("Could not send game request");
			}
		} else if (e.getSource() == sendChat) {
			if (!outwardChat.getText().equals("")) {
				try {
					client.getProtocoller().cmdChat(outwardChat.getText());
				} catch (IOException e1) {
					System.err.println("Error while sending chat");
					internalMessage("Something went wrong while sending chat");
				}
			}
		} else if (e.getSource() == addressOK) {
			lock.lock();
			try {
				addressInput = jtf.getText();
				addressInputted.signal();
			} finally {
				lock.unlock();
			}
		}
	}

	private String addressInput = null;
	private JButton addressOK;
	private JTextField jtf;
	private JDialog jd;
	private static ReentrantLock lock = new ReentrantLock();
	private static Condition addressInputted = lock.newCondition();
	synchronized public String getAddress() {
		lock.lock();
		try {
			jd = new JDialog(frame, "User input", false);
			jd.setLayout(new BorderLayout());
			JTextPane jtp = new JTextPane();
			jtp.setEditable(false);
			jtp.setText("Please input the server address:");
			jd.add(BorderLayout.NORTH, jtp);
			jtf = new JTextField();
			jd.add(BorderLayout.CENTER, jtf);
			addressOK = new JButton("OK");
			addressOK.addActionListener(this);
			jd.add(BorderLayout.EAST, addressOK);
			jd.pack();
			jd.setVisible(true);
			try {
				addressInputted.await(TUIController.MESSAGE_FREQUENCY, TimeUnit.SECONDS);
			} catch (InterruptedException e) {
				System.err.println("Got interrupted");
			}
			jd.dispose();
			return addressInput;
		} finally {
			lock.unlock();
		}
	}
	
	public String getMove() {
		return (String) JOptionPane.showInputDialog(frame, "Please give your move");
	}
	
	public void close() {
		frame.dispose();
	}
}
